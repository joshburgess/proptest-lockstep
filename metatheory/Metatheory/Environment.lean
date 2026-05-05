/-
  Typed Environment Formalization

  Models the TypedEnv variable environment that threads through
  lockstep execution. The Rust `TypedEnv` is a heterogeneous map
  using `Box<dyn Any>` with runtime type checks. This formalization
  abstracts over the implementation details, modeling the environment
  as an opaque state that is extended after each step.

  The key result: `env_runner_bounded_bisim_equiv` -- the runner
  correspondence theorem still holds when the environment is
  modeled explicitly. This closes the gap identified by reviewers:
  the formal guarantee now covers environment-threaded execution.

  Corresponds to `TypedEnv` in `src/env.rs` and the environment
  threading in `src/runner.rs`.
-/

import Metatheory.Lockstep

-- =========================================================================
-- Environment-aware system
-- =========================================================================

/--
  A lockstep system with explicit environment threading.

  The environment is an abstract state that accumulates results
  from previous steps. Each step receives the current environment
  and produces a result that extends the environment.

  This models the Rust runner's TypedEnv:
  - `store_model` extends the model environment after each step
  - `store_sut` extends the SUT environment after each step
  - Step functions receive the environment for variable resolution
-/
structure EnvLockstepSystem where
  SM : Type              -- model state
  SS : Type              -- SUT state
  Env : Type             -- environment (TypedEnv)
  ActionIdx : Type       -- action index
  RetM : ActionIdx → Type
  RetS : ActionIdx → Type
  bridge : (a : ActionIdx) → Bridge (RetS a) (RetM a)
  empty_env : Env
  step_model : (a : ActionIdx) → SM → Env → SM × RetM a
  step_sut : (a : ActionIdx) → SS → Env → SS × RetS a
  store_model : Env → (a : ActionIdx) → RetM a → Env
  store_sut : Env → (a : ActionIdx) → RetS a → Env

-- =========================================================================
-- Environment-aware bounded bisimulation
-- =========================================================================

/--
  Bounded bisimulation with explicit environment threading.

  Like `bounded_bisim` but the environment is threaded through
  each step: results are stored in the environment, and subsequent
  steps can access previous results via the environment.

  This directly models what the Rust runner does:
  1. Run step_model with the current environment
  2. Run step_sut with the current environment
  3. Check bridge_equiv on results
  4. Store results in the environment
  5. Continue with updated environment
-/
def env_bounded_bisim (sys : EnvLockstepSystem) :
    Nat → sys.SM → sys.SS → sys.Env → sys.Env → Prop
  | 0, _, _, _, _ => True
  | n + 1, sm, ss, menv, senv =>
    ∀ (a : sys.ActionIdx),
      let (sm', rm) := sys.step_model a sm menv
      let (ss', rs) := sys.step_sut a ss senv
      bridge_equiv (sys.bridge a) rs rm
      ∧ env_bounded_bisim sys n sm'  ss'
          (sys.store_model menv a rm)
          (sys.store_sut senv a rs)

-- =========================================================================
-- Environment-aware runner
-- =========================================================================

/--
  The runner with environment threading. Mirrors `LockstepSut::apply`:
  run model, run SUT, check bridge, store results in environments,
  continue with successor states and updated environments.
-/
def env_runner_passes (sys : EnvLockstepSystem) :
    List sys.ActionIdx → sys.SM → sys.SS → sys.Env → sys.Env → Prop
  | [], _, _, _, _ => True
  | a :: rest, sm, ss, menv, senv =>
    let (sm', rm) := sys.step_model a sm menv
    let (ss', rs) := sys.step_sut a ss senv
    bridge_equiv (sys.bridge a) rs rm
    ∧ env_runner_passes sys rest sm' ss'
        (sys.store_model menv a rm)
        (sys.store_sut senv a rs)

-- =========================================================================
-- Properties
-- =========================================================================

/-- Environment-aware bisim at depth 0 is trivially true. -/
theorem env_bisim_zero (sys : EnvLockstepSystem)
    (sm : sys.SM) (ss : sys.SS) (me : sys.Env) (se : sys.Env) :
    env_bounded_bisim sys 0 sm ss me se :=
  trivial

/-- Empty environment runner trace is trivially true. -/
theorem env_runner_nil (sys : EnvLockstepSystem)
    (sm : sys.SM) (ss : sys.SS) (me : sys.Env) (se : sys.Env) :
    env_runner_passes sys [] sm ss me se :=
  trivial

-- =========================================================================
-- Runner correspondence with environments
-- =========================================================================

/--
  **Forward direction**: if the environment-aware runner passes on
  ALL traces of length n, then environment-aware bisimulation holds.

  This is the environment-threaded version of
  `runner_implies_bounded_bisim`.
-/
theorem env_runner_implies_bisim (sys : EnvLockstepSystem)
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (menv : sys.Env) (senv : sys.Env)
    (h : ∀ (trace : List sys.ActionIdx), trace.length = n →
         env_runner_passes sys trace sm ss menv senv) :
    env_bounded_bisim sys n sm ss menv senv := by
  induction n generalizing sm ss menv senv with
  | zero => trivial
  | succ k ih =>
    simp only [env_bounded_bisim]
    intro a
    have hcons : ∀ (rest : List sys.ActionIdx), rest.length = k →
        env_runner_passes sys (a :: rest) sm ss menv senv := by
      intro rest hlen
      exact h (a :: rest) (by simp [hlen])
    have hany := hcons (List.replicate k a) (by simp)
    simp only [env_runner_passes] at hany
    obtain ⟨hbridge, _⟩ := hany
    constructor
    · exact hbridge
    · apply ih
      intro rest hlen
      have := hcons rest hlen
      simp only [env_runner_passes] at this
      exact this.2

/--
  **Reverse direction**: if environment-aware bisimulation holds,
  the runner passes on any trace of that length.
-/
theorem env_bisim_implies_runner (sys : EnvLockstepSystem)
    (trace : List sys.ActionIdx)
    (sm : sys.SM) (ss : sys.SS)
    (menv : sys.Env) (senv : sys.Env)
    (h : env_bounded_bisim sys trace.length sm ss menv senv) :
    env_runner_passes sys trace sm ss menv senv := by
  induction trace generalizing sm ss menv senv with
  | nil => trivial
  | cons a rest ih =>
    simp only [env_runner_passes]
    simp only [List.length, env_bounded_bisim] at h
    have ha := h a
    exact ⟨ha.1, ih _ _ _ _ ha.2⟩

/--
  **Environment-aware runner correspondence (biconditional).**

  Passing on all traces of length n is equivalent to environment-
  aware bounded bisimulation at depth n. This is the full
  environment-threaded version of `runner_bounded_bisim_equiv`.

  This closes the TypedEnv gap: the formal guarantee now covers
  environment-threaded execution, matching what the Rust runner
  actually does.
-/
theorem env_runner_bounded_bisim_equiv (sys : EnvLockstepSystem)
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (menv : sys.Env) (senv : sys.Env) :
    (∀ (trace : List sys.ActionIdx), trace.length = n →
     env_runner_passes sys trace sm ss menv senv)
    ↔ env_bounded_bisim sys n sm ss menv senv := by
  constructor
  · exact env_runner_implies_bisim sys n sm ss menv senv
  · intro h trace hlen
    have : env_bounded_bisim sys trace.length sm ss menv senv := by
      rw [hlen]; exact h
    exact env_bisim_implies_runner sys trace sm ss menv senv this

-- =========================================================================
-- Relationship to environment-free bisimulation
-- =========================================================================

/--
  **Forgetting environments**: any environment-free `LockstepSystem`
  can be lifted to an `EnvLockstepSystem` with a trivial (Unit)
  environment. The resulting bisimulation is equivalent to the
  original `bounded_bisim`.

  This shows that the environment-aware formalization is a strict
  generalization: it reduces to the environment-free version when
  the environment is trivial.
-/
def lift_to_env (sys : LockstepSystem) : EnvLockstepSystem where
  SM := sys.SM
  SS := sys.SS
  Env := Unit
  ActionIdx := sys.ActionIdx
  RetM := sys.RetM
  RetS := sys.RetS
  bridge := sys.bridge
  empty_env := ()
  step_model := fun a sm _ => sys.step_model a sm
  step_sut := fun a ss _ => sys.step_sut a ss
  store_model := fun _ _ _ => ()
  store_sut := fun _ _ _ => ()

theorem lift_bisim_equiv (sys : LockstepSystem)
    (n : Nat) (sm : sys.SM) (ss : sys.SS) :
    bounded_bisim sys n sm ss
    ↔ env_bounded_bisim (lift_to_env sys) n sm ss () () := by
  induction n generalizing sm ss with
  | zero => simp [bounded_bisim, env_bounded_bisim]
  | succ k ih =>
    simp only [bounded_bisim, env_bounded_bisim, lift_to_env]
    constructor
    · intro h a
      have ha := h a
      exact ⟨ha.1, (ih _ _).mp ha.2⟩
    · intro h a
      have ha := h a
      exact ⟨ha.1, (ih _ _).mpr ha.2⟩
