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

-- =========================================================================
-- Bug localization
-- =========================================================================

/--
  **Bug localization**: if bounded bisimulation fails at depth n+1,
  then either the bridge check fails at the current state for some
  action, or the bisimulation fails at depth n at some successor
  state. This gives a way to localize where the bug manifests.

  Note: this theorem uses classical logic (`Classical.byContradiction`)
  because extracting an existential witness from `¬∀` requires excluded
  middle when `ActionIdx` is not assumed finite. The bridge conjunct
  IS decidable (via `bridge_equiv_decidable`), but `bounded_bisim` at
  the successor may not be.
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
      -- Use decidability of bridge_equiv for the first conjunct
      have hbridge : bridge_equiv (sys.bridge a)
          (sys.step_sut a ss).2 (sys.step_model a sm).2 := by
        exact Decidable.byContradiction fun h => hna (Or.inl h)
      have hbisim : bounded_bisim sys n
          (sys.step_model a sm).1 (sys.step_sut a ss).1 := by
        exact Classical.byContradiction fun h => hna (Or.inr h)
      exact ⟨hbridge, hbisim⟩)

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

-- The full testing guarantee (soundness + completeness) is the
-- biconditional `observational_refinement_equiv` in
-- ObservationalRefinement.lean:
--   bounded_bisim n sm ss ↔ ∀ pre a, |pre|+1 ≤ n → obs_sut = obs_model
