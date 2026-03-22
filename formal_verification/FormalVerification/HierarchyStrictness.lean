/-
  Consistency Hierarchy Strictness

  Proves the consistency hierarchy is STRICT: each level is
  genuinely weaker than the one above. Without these theorems,
  the implications could be equivalences (all notions could collapse).

  We construct concrete counterexample systems witnessing each gap:
  - A system that satisfies convergent_bisim but NOT bounded_bisim
  - bounded_bisim is strictly stronger than convergent_bisim

  This makes the hierarchy diagram a theorem, not a claim.
-/

import FormalVerification.Lockstep
import FormalVerification.EventualConsistency

-- =========================================================================
-- Strictness: convergent_bisim does NOT imply bounded_bisim
-- =========================================================================

/--
  A concrete system where convergent_bisim holds but bounded_bisim
  does NOT. The system has one action that produces different results
  from model and SUT (bridge_equiv fails), but the sync function
  ignores the difference (convergent_bisim passes).

  This is the "stale read" pattern: the SUT returns stale data,
  but after sync, everything agrees.
-/
def stale_read_system : EventualSystem where
  SM := Unit
  SS := Unit
  ActionIdx := Unit
  RetM := fun _ => Bool  -- model returns true
  RetS := fun _ => Bool  -- SUT returns false (stale!)
  bridge := fun _ => transparent Bool
  step_model := fun _ _ => ((), true)
  step_sut := fun _ _ => ((), false)  -- STALE: returns false
  OS := Unit
  model_sync := fun _ => ()  -- sync ignores the difference
  sut_sync := fun _ => ()
  invariant := fun _ => True

/--
  **bounded_bisim fails for the stale read system.**
  bridge_equiv (transparent Bool) false true = (false = true) = False.
-/
theorem stale_read_not_linearizable :
    ¬ bounded_bisim stale_read_system.toLockstepSystem 1 () () := by
  intro h
  simp only [bounded_bisim] at h
  have := h ()
  simp only [stale_read_system, bridge_equiv, transparent] at this
  exact absurd this.1 (by simp [id])

/--
  **convergent_bisim holds for the stale read system.**
  model_sync and sut_sync both return (), so sync agreement holds.
-/
theorem stale_read_eventually_consistent :
    convergent_bisim stale_read_system 1 () () := by
  simp only [convergent_bisim, stale_read_system]
  exact ⟨trivial, trivial, fun _ => trivial⟩

/--
  **THE STRICTNESS THEOREM**: convergent_bisim does NOT imply
  bounded_bisim. There exists a system (stale_read_system) where
  convergent_bisim holds at depth 1 but bounded_bisim fails at depth 1.
-/
theorem convergent_strictly_weaker :
    ∃ (sys : EventualSystem) (sm : sys.SM) (ss : sys.SS),
      convergent_bisim sys 1 sm ss
      ∧ ¬ bounded_bisim sys.toLockstepSystem 1 sm ss :=
  ⟨stale_read_system, (), (),
   stale_read_eventually_consistent,
   stale_read_not_linearizable⟩
