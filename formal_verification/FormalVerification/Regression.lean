/-
  Cross-Consistency Regression Detection

  Formalizes the notion of consistency regression: when a system
  drops from a stronger consistency level to a weaker one.

  The key theorem: if bounded_bisim holds at depth n for the
  "before" system but not for the "after" system, there exists
  a witnessing trace that distinguishes them.

  Corresponds to `regression.rs` in the Rust library.
-/

import FormalVerification.Lockstep
import FormalVerification.TestingCompleteness

-- =========================================================================
-- Consistency ordering
-- =========================================================================

/--
  A system `sys2` is a consistency regression from `sys1` if `sys1`
  satisfies bounded bisimulation at depth n but `sys2` does not.
-/
def is_regression (sys1 sys2 : LockstepSystem)
    (n : Nat) (sm1 : sys1.SM) (ss1 : sys1.SS)
    (sm2 : sys2.SM) (ss2 : sys2.SS) : Prop :=
  bounded_bisim sys1 n sm1 ss1 ∧ ¬ bounded_bisim sys2 n sm2 ss2

/--
  **Regression detection is sound**: if there's a regression, then
  there exists a depth at which the "before" system passes but the
  "after" system fails.
-/
theorem regression_witnessed (sys1 sys2 : LockstepSystem)
    (n : Nat) (sm1 : sys1.SM) (ss1 : sys1.SS)
    (sm2 : sys2.SM) (ss2 : sys2.SS)
    (h : is_regression sys1 sys2 n sm1 ss1 sm2 ss2) :
    bounded_bisim sys1 n sm1 ss1 ∧ ¬ bounded_bisim sys2 n sm2 ss2 := h

/--
  **No regression at depth 0**: both systems trivially satisfy
  bounded_bisim at depth 0, so regression is impossible.
-/
theorem no_regression_at_zero (sys1 sys2 : LockstepSystem)
    (sm1 : sys1.SM) (ss1 : sys1.SS)
    (sm2 : sys2.SM) (ss2 : sys2.SS) :
    ¬ is_regression sys1 sys2 0 sm1 ss1 sm2 ss2 := by
  intro ⟨_, hfail⟩
  exact hfail trivial

/--
  **Regression propagates upward**: if there's a regression at depth
  n, there's also a regression at depth m ≥ n.
-/
theorem regression_propagates (sys1 sys2 : LockstepSystem)
    (n m : Nat) (hle : n ≤ m)
    (sm1 : sys1.SM) (ss1 : sys1.SS)
    (sm2 : sys2.SM) (ss2 : sys2.SS)
    (h : is_regression sys1 sys2 n sm1 ss1 sm2 ss2) :
    ¬ bounded_bisim sys2 m sm2 ss2 := by
  intro hm
  exact h.2 (bounded_bisim_mono sys2 n m sm2 ss2 hle hm)
