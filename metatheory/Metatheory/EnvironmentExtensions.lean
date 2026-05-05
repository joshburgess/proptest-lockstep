/-
  Environment-Aware Extensions

  Lifts key extensions from `LockstepSystem` (environment-free)
  to `EnvLockstepSystem` (environment-threaded). This connects
  the environment formalization to the extension modules, closing
  the "island" gap.

  The key insight: each extension's bisimulation variant can be
  lifted to the environment-aware setting by adding environment
  parameters to the state threading. The `lift_to_env` function
  from `Environment.lean` shows the environment-free case is a
  special case (Unit environment).
-/

import Metatheory.Environment
import Metatheory.CrashRecovery
import Metatheory.Compositional
import Metatheory.SessionConsistency

-- =========================================================================
-- Environment-aware crash-recovery
-- =========================================================================

/--
  An environment-aware crash-recovery system.
  Extends EnvLockstepSystem with crash/recovery semantics.
-/
structure EnvCrashRecoverySystem extends EnvLockstepSystem where
  DS : Type
  checkpoint : SM → DS
  model_recover : DS → SM
  sut_recover : SS → SS
  env_reset : Env  -- environment after crash (typically empty_env)
  invariant : SM → Prop

/--
  Environment-aware crash bisimulation.
  Like crash_bisim but with environment threading.
-/
def env_crash_bisim (sys : EnvCrashRecoverySystem) :
    Nat → sys.SM → sys.SS → sys.Env → sys.Env → Prop
  | 0, _, _, _, _ => True
  | n + 1, sm, ss, menv, senv =>
    sys.invariant sm
    ∧ (∀ (a : sys.ActionIdx),
        let (sm', rm) := sys.step_model a sm menv
        let (ss', rs) := sys.step_sut a ss senv
        bridge_equiv (sys.bridge a) rs rm
        ∧ env_crash_bisim sys n sm' ss'
            (sys.store_model menv a rm)
            (sys.store_sut senv a rs))
    ∧ env_crash_bisim sys n
        (sys.model_recover (sys.checkpoint sm))
        (sys.sut_recover ss)
        sys.env_reset sys.env_reset

/--
  **Env crash bisim implies env bounded bisim**: crash-recovery
  bisimulation with environments is stronger than plain
  environment-aware bounded bisimulation.
-/
theorem env_crash_implies_env_bounded (sys : EnvCrashRecoverySystem)
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (menv : sys.Env) (senv : sys.Env)
    (h : env_crash_bisim sys n sm ss menv senv) :
    env_bounded_bisim sys.toEnvLockstepSystem n sm ss menv senv := by
  induction n generalizing sm ss menv senv with
  | zero => trivial
  | succ k ih =>
    simp only [env_crash_bisim] at h
    obtain ⟨_, hactions, _⟩ := h
    simp only [env_bounded_bisim]
    intro a
    have ha := hactions a
    exact ⟨ha.1, ih _ _ _ _ ha.2⟩

-- =========================================================================
-- Environment-aware compositional bisimulation
-- =========================================================================

/--
  The product of two environment-aware systems. Each subsystem
  has its own environment; actions from one don't affect the other.
-/
def env_product_system (sys1 sys2 : EnvLockstepSystem) :
    EnvLockstepSystem where
  SM := sys1.SM × sys2.SM
  SS := sys1.SS × sys2.SS
  Env := sys1.Env × sys2.Env
  ActionIdx := sys1.ActionIdx ⊕ sys2.ActionIdx
  RetM := fun
    | .inl a => sys1.RetM a
    | .inr a => sys2.RetM a
  RetS := fun
    | .inl a => sys1.RetS a
    | .inr a => sys2.RetS a
  bridge := fun
    | .inl a => sys1.bridge a
    | .inr a => sys2.bridge a
  empty_env := (sys1.empty_env, sys2.empty_env)
  step_model := fun
    | .inl a => fun (sm1, sm2) (e1, _) =>
        let (sm1', r) := sys1.step_model a sm1 e1
        ((sm1', sm2), r)
    | .inr a => fun (sm1, sm2) (_, e2) =>
        let (sm2', r) := sys2.step_model a sm2 e2
        ((sm1, sm2'), r)
  step_sut := fun
    | .inl a => fun (ss1, ss2) (e1, _) =>
        let (ss1', r) := sys1.step_sut a ss1 e1
        ((ss1', ss2), r)
    | .inr a => fun (ss1, ss2) (_, e2) =>
        let (ss2', r) := sys2.step_sut a ss2 e2
        ((ss1, ss2'), r)
  store_model := fun (e1, e2) =>
    fun
    | .inl a => fun r => (sys1.store_model e1 a r, e2)
    | .inr a => fun r => (e1, sys2.store_model e2 a r)
  store_sut := fun (e1, e2) =>
    fun
    | .inl a => fun r => (sys1.store_sut e1 a r, e2)
    | .inr a => fun r => (e1, sys2.store_sut e2 a r)

/--
  **Environment-aware compositional bisimulation**: if both
  environment-aware subsystems satisfy env_bounded_bisim, their
  product does too.
-/
theorem env_compositional_bisim (sys1 sys2 : EnvLockstepSystem)
    (n : Nat)
    (sm1 : sys1.SM) (ss1 : sys1.SS) (me1 : sys1.Env) (se1 : sys1.Env)
    (sm2 : sys2.SM) (ss2 : sys2.SS) (me2 : sys2.Env) (se2 : sys2.Env)
    (h1 : env_bounded_bisim sys1 n sm1 ss1 me1 se1)
    (h2 : env_bounded_bisim sys2 n sm2 ss2 me2 se2) :
    env_bounded_bisim (env_product_system sys1 sys2) n
      (sm1, sm2) (ss1, ss2) (me1, me2) (se1, se2) := by
  induction n generalizing sm1 ss1 me1 se1 sm2 ss2 me2 se2 with
  | zero => trivial
  | succ k ih =>
    simp only [env_bounded_bisim]
    intro a
    match a with
    | .inl a1 =>
      simp only [env_product_system]
      simp only [env_bounded_bisim] at h1
      have ha1 := h1 a1
      have h2k := env_bisim_mono sys2 k (k + 1) sm2 ss2 me2 se2 (by omega) h2
      exact ⟨ha1.1, ih _ _ _ _ _ _ _ _ ha1.2 h2k⟩
    | .inr a2 =>
      simp only [env_product_system]
      simp only [env_bounded_bisim] at h2
      have ha2 := h2 a2
      have h1k := env_bisim_mono sys1 k (k + 1) sm1 ss1 me1 se1 (by omega) h1
      exact ⟨ha2.1, ih _ _ _ _ _ _ _ _ h1k ha2.2⟩

where
  env_bisim_mono (sys : EnvLockstepSystem) :
      ∀ (n m : Nat) (sm : sys.SM) (ss : sys.SS) (me se : sys.Env),
      n ≤ m → env_bounded_bisim sys m sm ss me se →
      env_bounded_bisim sys n sm ss me se := by
    intro n
    induction n with
    | zero => intros; trivial
    | succ k ih =>
      intro m sm ss me se h hm
      match m, h with
      | m' + 1, h' =>
        simp only [env_bounded_bisim] at hm ⊢
        intro a
        have ha := hm a
        exact ⟨ha.1, ih m' _ _ _ _ (by omega) ha.2⟩

-- =========================================================================
-- Crash-recovery + session consistency composition
-- =========================================================================

/--
  A system supporting both crash-recovery and session consistency.
  After a crash, session histories reset to empty -- the session
  sees a "fresh start" on recovery.
-/
structure CrashSessionSystem extends CrashRecoverySystem where
  Session : Type
  Key : Type
  Obs : Type
  session_of : ActionIdx → Option Session
  read_key : ActionIdx → Option Key
  sut_read_obs : ActionIdx → SS → Option Obs
  write_key : ActionIdx → Option Key
  write_val : ActionIdx → Option Obs

/--
  Extract the underlying SessionSystem from a CrashSessionSystem.
-/
abbrev CrashSessionSystem.toSessionSystem (sys : CrashSessionSystem) :
    SessionSystem where
  SM := sys.SM
  SS := sys.SS
  ActionIdx := sys.ActionIdx
  RetM := sys.RetM
  RetS := sys.RetS
  bridge := sys.bridge
  step_model := sys.step_model
  step_sut := sys.step_sut
  Session := sys.Session
  Key := sys.Key
  Obs := sys.Obs
  session_of := sys.session_of
  read_key := sys.read_key
  sut_read_obs := sys.sut_read_obs
  write_key := sys.write_key
  write_val := sys.write_val

/--
  **Crash-session bisimulation** with proper history interaction:
  after a crash, session histories reset to empty. This captures
  the key invariant: a client reconnecting after crash gets a fresh
  session with no prior write/read history.

  Unlike the simple conjunction `crash_bisim ∧ session_bisim`, this
  definition threads histories through the crash transition,
  resetting them to `empty_histories` on recovery.
-/
def crash_session_bisim (sys : CrashSessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key] :
    Nat → sys.SM → sys.SS →
    SessionHistories sys.Session sys.Key sys.Obs → Prop
  | 0, _, _, _ => True
  | n + 1, sm, ss, hists =>
    -- Invariant holds
    sys.invariant sm
    -- Normal actions: RYW + bridge + recursion with updated histories
    ∧ (∀ (a : sys.ActionIdx),
        (match sys.session_of a, sys.read_key a, sys.sut_read_obs a ss with
          | some s, some k, some obs => read_your_writes (hists s) k obs
          | _, _, _ => True)
        ∧ bridge_equiv (sys.bridge a)
          (sys.step_sut a ss).2 (sys.step_model a sm).2
        ∧ crash_session_bisim sys n
          (sys.step_model a sm).1 (sys.step_sut a ss).1
          (match sys.session_of a, sys.write_key a, sys.write_val a with
            | some s, some k, some v =>
              fun s' => if s' = s then update_write (hists s) k v else hists s'
            | _, _, _ => hists))
    -- CRASH: recovered states with EMPTY histories (fresh session)
    ∧ crash_session_bisim sys n
        (sys.model_recover (sys.checkpoint sm))
        (sys.sut_recover ss)
        (empty_histories sys.Session sys.Key sys.Obs)

/--
  **Crash-session implies crash**: forgetting session histories
  gives the underlying crash bisimulation.
-/
theorem crash_session_implies_crash (sys : CrashSessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (hists : SessionHistories sys.Session sys.Key sys.Obs)
    (h : crash_session_bisim sys n sm ss hists) :
    crash_bisim sys.toCrashRecoverySystem n sm ss := by
  induction n generalizing sm ss hists with
  | zero => trivial
  | succ k ih =>
    simp only [crash_session_bisim] at h
    obtain ⟨hinv, hactions, hcrash⟩ := h
    simp only [crash_bisim]
    refine ⟨hinv, ?_, ih _ _ _ hcrash⟩
    intro a
    have ha := hactions a
    exact ⟨ha.2.1, ih _ _ _ ha.2.2⟩

/--
  **Crash-session implies bounded**: crash-session bisimulation
  implies plain bounded bisimulation (via crash → bounded).
-/
theorem crash_session_implies_bounded (sys : CrashSessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (hists : SessionHistories sys.Session sys.Key sys.Obs)
    (h : crash_session_bisim sys n sm ss hists) :
    bounded_bisim sys.toLockstepSystem n sm ss :=
  crash_bisim_implies_bounded sys.toCrashRecoverySystem n sm ss
    (crash_session_implies_crash sys n sm ss hists h)
