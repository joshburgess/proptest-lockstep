/-
  Observational Refinement

  The central theoretical result: bounded bisimulation implies
  observational indistinguishability. If bounded_bisim holds at
  depth n, then for any sequence of ≤ n actions, the bridge
  observations produced by the SUT and model are identical.

  This makes the "observational refinement" guarantee explicit:
  the SUT refines the model at the level of observable behavior,
  where "observable" is determined by the bridge algebra.

  This connects to Reynolds' abstraction theorem (1983): bridge_equiv
  is a logical relation, and bounded bisimulation ensures that any
  interaction through the bridge API cannot distinguish the SUT
  from the model.
-/

import FormalVerification.Runner

-- =========================================================================
-- Single-step observations
-- =========================================================================

/-- The model's observation: apply bridge observation to model result. -/
def model_observation (sys : LockstepSystem) (a : sys.ActionIdx)
    (sm : sys.SM) : (sys.bridge a).Observed :=
  (sys.bridge a).observe_model (sys.step_model a sm).2

/-- The SUT's observation: apply bridge observation to SUT result. -/
def sut_observation (sys : LockstepSystem) (a : sys.ActionIdx)
    (ss : sys.SS) : (sys.bridge a).Observed :=
  (sys.bridge a).observe_real (sys.step_sut a ss).2

/--
  **Single-step observational refinement**: if bounded bisimulation
  holds at depth n+1, then for any action, the SUT and model produce
  the same observation.

  This is bridge_equiv restated in terms of the Observed type,
  making the "observational equivalence" explicit.
-/
theorem bisim_implies_equal_observation (sys : LockstepSystem)
    (sm : sys.SM) (ss : sys.SS) (a : sys.ActionIdx) (n : Nat)
    (h : bounded_bisim sys (n + 1) sm ss) :
    sut_observation sys a ss = model_observation sys a sm := by
  simp only [sut_observation, model_observation, bounded_bisim] at *
  exact (h a).1

-- =========================================================================
-- Trace-level observations
-- =========================================================================

/-- Model state after running a trace. -/
def model_state_after (sys : LockstepSystem) :
    List sys.ActionIdx → sys.SM → sys.SM
  | [], sm => sm
  | a :: rest, sm => model_state_after sys rest (sys.step_model a sm).1

/-- SUT state after running a trace. -/
def sut_state_after (sys : LockstepSystem) :
    List sys.ActionIdx → sys.SS → sys.SS
  | [], ss => ss
  | a :: rest, ss => sut_state_after sys rest (sys.step_sut a ss).1

/--
  **Observation after prefix**: if bounded bisimulation holds at
  sufficient depth, then after running any prefix of actions, the
  observations at the resulting states are still equal.

  This is the key trace-level result: the SUT and model stay
  observationally equivalent throughout the entire execution, not
  just at the initial state.
-/
theorem bisim_observation_after_prefix (sys : LockstepSystem)
    (pre : List sys.ActionIdx) (a : sys.ActionIdx)
    (sm : sys.SM) (ss : sys.SS)
    (h : bounded_bisim sys (pre.length + 1) sm ss) :
    sut_observation sys a (sut_state_after sys pre ss)
    = model_observation sys a (model_state_after sys pre sm) := by
  induction pre generalizing sm ss with
  | nil =>
    simp [model_state_after, sut_state_after]
    exact bisim_implies_equal_observation sys sm ss a _ h
  | cons b rest ih =>
    simp only [model_state_after, sut_state_after]
    apply ih
    simp only [bounded_bisim] at h
    exact (h b).2

/--
  **Bisimulation preserved along trace**: if bounded bisimulation
  holds at depth n + k, then after running a prefix of length k,
  bounded bisimulation at depth n holds on the successor states.
-/
theorem bisim_along_trace (sys : LockstepSystem)
    (trace : List sys.ActionIdx) (n : Nat)
    (sm : sys.SM) (ss : sys.SS)
    (h : bounded_bisim sys (trace.length + n) sm ss) :
    bounded_bisim sys n
      (model_state_after sys trace sm)
      (sut_state_after sys trace ss) := by
  induction trace generalizing sm ss with
  | nil =>
    simp only [model_state_after, sut_state_after]
    simpa using h
  | cons a rest ih =>
    simp only [model_state_after, sut_state_after]
    apply ih
    have hlen : (a :: rest).length + n = (rest.length + n) + 1 := by
      simp; omega
    rw [hlen] at h
    simp only [bounded_bisim] at h
    exact (h a).2

-- =========================================================================
-- Observational refinement (the free theorem)
-- =========================================================================

/--
  **Observational refinement**: bounded bisimulation at depth n
  guarantees that the SUT observationally refines the model for
  all interactions of depth ≤ n.

  Specifically: for any prefix of length < n and any action at
  the resulting state, the bridge observation is identical. No
  interaction through the bridge API can distinguish the SUT
  from the model within the tested depth.

  This is the formal statement of the claim in theory.rs:
  "a passing lockstep test proves observational refinement."
-/
theorem observational_refinement (sys : LockstepSystem)
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (h : bounded_bisim sys n sm ss)
    (pre : List sys.ActionIdx) (a : sys.ActionIdx)
    (hdepth : pre.length + 1 ≤ n) :
    sut_observation sys a (sut_state_after sys pre ss)
    = model_observation sys a (model_state_after sys pre sm) := by
  apply bisim_observation_after_prefix
  have hmono := bounded_bisim_mono sys (pre.length + 1) n sm ss hdepth h
  exact hmono

/--
  **Full trace observational refinement**: at every step along
  a trace of length ≤ n, the observations are identical.
-/
theorem full_trace_refinement (sys : LockstepSystem)
    (trace : List sys.ActionIdx)
    (sm : sys.SM) (ss : sys.SS)
    (h : bounded_bisim sys trace.length sm ss) :
    runner_passes sys trace sm ss := by
  exact bounded_bisim_implies_runner sys trace sm ss h

-- =========================================================================
-- Connecting to the runner
-- =========================================================================

/--
  **Observational refinement ↔ runner passes**: the system
  observationally refines the model at depth n iff the runner
  passes on all traces of length n. This closes the circle:

    runner passes ↔ bounded_bisim ↔ observational refinement
-/
theorem observational_refinement_equiv (sys : LockstepSystem)
    (n : Nat) (sm : sys.SM) (ss : sys.SS) :
    bounded_bisim sys n sm ss
    ↔ (∀ (pre : List sys.ActionIdx) (a : sys.ActionIdx),
        pre.length + 1 ≤ n →
        sut_observation sys a (sut_state_after sys pre ss)
        = model_observation sys a (model_state_after sys pre sm)) := by
  constructor
  · intro h pre a hdepth
    exact observational_refinement sys n sm ss h pre a hdepth
  · intro h
    induction n generalizing sm ss with
    | zero => trivial
    | succ k ih =>
      simp only [bounded_bisim]
      intro a
      constructor
      · -- Bridge equiv at this step
        have := h [] a (by simp)
        simp [sut_state_after, model_state_after, sut_observation,
              model_observation] at this
        exact this
      · -- Bisim at successor
        apply ih
        intro pre a' hdepth
        have := h (a :: pre) a' (by simp; omega)
        simp [sut_state_after, model_state_after] at this
        exact this
