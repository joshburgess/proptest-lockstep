/-
  Testing Completeness

  The contrapositive of observational refinement: any observable
  discrepancy between the SUT and model WILL be detected by the
  runner at sufficient depth. This is the "no false negatives"
  guarantee — if a bug is observable through the bridge algebra,
  lockstep testing will find it.

  Combined with soundness (Runner.lean) and observational refinement
  (ObservationalRefinement.lean), this gives the full picture:

    runner passes ↔ bounded_bisim ↔ observational refinement
    ¬ observational refinement → ¬ bounded_bisim → runner fails

  The depth at which the bug is detected equals the length of the
  action prefix that exposes it, plus one.
-/

import FormalVerification.ObservationalRefinement
import FormalVerification.OpaqueDetection

-- =========================================================================
-- Testing completeness
-- =========================================================================

/--
  **Testing completeness**: if the SUT and model produce different
  observations after some prefix of actions, then bounded bisimulation
  fails at depth `prefix.length + 1`.

  This means: any bug that is observable through the bridge algebra
  will be caught by lockstep testing at sufficient depth. There are
  no false negatives — only insufficient depth.
-/
theorem testing_completeness (sys : LockstepSystem)
    (sm : sys.SM) (ss : sys.SS)
    (pre : List sys.ActionIdx) (a : sys.ActionIdx)
    (hbug : sut_observation sys a (sut_state_after sys pre ss)
            ≠ model_observation sys a (model_state_after sys pre sm)) :
    ¬ bounded_bisim sys (pre.length + 1) sm ss := by
  intro hbisim
  exact hbug (observational_refinement sys (pre.length + 1) sm ss
    hbisim pre a (by omega))

/--
  **Failure propagation**: if a bug exists at depth k, the runner
  will fail on any trace of length ≥ k that reaches the buggy state.
  Testing at greater depth never misses a bug found at lesser depth.
-/
theorem bug_detected_at_all_greater_depths (sys : LockstepSystem)
    (sm : sys.SM) (ss : sys.SS) (n : Nat)
    (hfail : ¬ bounded_bisim sys n sm ss)
    (m : Nat) (hge : n ≤ m) :
    ¬ bounded_bisim sys m sm ss :=
  failure_propagates_up sys sm ss n m hge hfail

-- =========================================================================
-- Bug localization
-- =========================================================================

/--
  **Bug localization**: if bounded bisimulation fails at depth n+1,
  then either the bridge check fails at the current state for some
  action, or the bisimulation fails at depth n at some successor
  state. This gives a way to localize where the bug manifests.
-/
theorem bug_localization (sys : LockstepSystem)
    (sm : sys.SM) (ss : sys.SS) (n : Nat)
    (hfail : ¬ bounded_bisim sys (n + 1) sm ss) :
    ∃ (a : sys.ActionIdx),
      ¬ bridge_equiv (sys.bridge a)
          (sys.step_sut a ss).2 (sys.step_model a sm).2
      ∨ ¬ bounded_bisim sys n
          (sys.step_model a sm).1 (sys.step_sut a ss).1 :=
  Classical.byContradiction fun hall =>
    hfail (by
      simp only [bounded_bisim]
      intro a
      have hna : ¬ (¬ bridge_equiv (sys.bridge a)
          (sys.step_sut a ss).2 (sys.step_model a sm).2
        ∨ ¬ bounded_bisim sys n
          (sys.step_model a sm).1 (sys.step_sut a ss).1) :=
        fun habs => hall ⟨a, habs⟩
      exact ⟨Classical.byContradiction fun h => hna (Or.inl h),
             Classical.byContradiction fun h => hna (Or.inr h)⟩)

/--
  **Immediate bug**: if the bridge check fails at the current state,
  bounded bisimulation fails at depth 1.
-/
theorem immediate_bug (sys : LockstepSystem)
    (sm : sys.SM) (ss : sys.SS) (a : sys.ActionIdx)
    (hfail : ¬ bridge_equiv (sys.bridge a)
        (sys.step_sut a ss).2 (sys.step_model a sm).2) :
    ¬ bounded_bisim sys 1 sm ss := by
  intro hbisim
  simp only [bounded_bisim] at hbisim
  exact hfail (hbisim a).1

-- =========================================================================
-- The full testing guarantee
-- =========================================================================

/--
  **The full testing guarantee**: lockstep testing is both sound and
  complete with respect to observational refinement.

  - **Sound**: if the runner passes on all traces of length n, the
    SUT observationally refines the model at depth n.
  - **Complete**: if the SUT does NOT observationally refine the model
    (some observation differs at depth ≤ n), the runner will fail on
    some trace of length n.

  Together: bounded_bisim is the exact characterization of
  "observationally indistinguishable up to depth n."
-/
theorem testing_sound_and_complete (sys : LockstepSystem)
    (n : Nat) (sm : sys.SM) (ss : sys.SS) :
    bounded_bisim sys n sm ss
    ↔ (∀ (pre : List sys.ActionIdx) (a : sys.ActionIdx),
        pre.length + 1 ≤ n →
        sut_observation sys a (sut_state_after sys pre ss)
        = model_observation sys a (model_state_after sys pre sm)) :=
  observational_refinement_equiv sys n sm ss
