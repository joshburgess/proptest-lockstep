/-
  Bridge-Indexed Testing Depth

  Formalizes the relationship between bridge structure and minimum
  testing depth. The key insight from `opaque_depth_sensitivity`:
  opaque bridges require deeper testing because wrong handles are
  only detected when USED later.

  The main theorem: if all bridges are transparent, depth 1 suffices
  for single-step detection. If any bridge is opaque, depth ≥ 2 is
  needed.

  Corresponds to `depth.rs` in the Rust library.
-/

import FormalVerification.OpaqueDetection
import FormalVerification.TestingCompleteness

-- =========================================================================
-- Depth sufficiency
-- =========================================================================

/--
  **Transparent depth 1 sufficiency**: if all bridges behave like
  transparent (bridge_equiv implies equality of observations), then
  depth 1 is sufficient to detect any single-step discrepancy.

  This follows from `single_step_bisim`: one-step bridge agreement
  implies bounded_bisim at depth 1.
-/
theorem transparent_depth_1 (sys : LockstepSystem)
    (sm : sys.SM) (ss : sys.SS)
    (h : ∀ a, bridge_equiv (sys.bridge a)
        (sys.step_sut a ss).2 (sys.step_model a sm).2) :
    bounded_bisim sys 1 sm ss :=
  single_step_bisim sys sm ss h

/--
  **Opaque depth 2 necessity**: there exist systems where depth 1
  passes but depth 2 fails (opaque bridges hide the discrepancy
  at depth 1). This is `opaque_depth_sensitivity` restated.
-/
theorem opaque_needs_depth_2 (sys : LockstepSystem)
    (sm : sys.SM) (ss : sys.SS)
    (hall_opaque : ∀ (a : sys.ActionIdx) rs rm,
        bridge_equiv (sys.bridge a) rs rm)
    (a b : sys.ActionIdx)
    (hb_fails : ¬ bridge_equiv (sys.bridge b)
        (sys.step_sut b (sys.step_sut a ss).1).2
        (sys.step_model b (sys.step_model a sm).1).2) :
    bounded_bisim sys 1 sm ss ∧ ¬ bounded_bisim sys 2 sm ss :=
  opaque_depth_sensitivity sys sm ss hall_opaque a b hb_fails

/--
  **Deeper testing is never weaker**: testing at depth m ≥ n
  gives at least as strong a guarantee. So recommending a higher
  depth is always safe (conservative).
-/
theorem deeper_is_stronger (sys : LockstepSystem)
    (n m : Nat) (hle : n ≤ m)
    (sm : sys.SM) (ss : sys.SS)
    (h : bounded_bisim sys m sm ss) :
    bounded_bisim sys n sm ss :=
  bounded_bisim_mono sys n m sm ss hle h

-- =========================================================================
-- Tight depth bounds
-- =========================================================================

/--
  **Depth 2 is exactly tight for opaque + immediate use.**
  Necessary (depth 1 passes) AND sufficient (depth 2 catches it).
  The minimum detection depth for a wrong opaque handle followed
  immediately by a discriminating action is EXACTLY 2.
-/
theorem opaque_detection_tight (sys : LockstepSystem)
    (sm : sys.SM) (ss : sys.SS)
    (hall_opaque : ∀ (a : sys.ActionIdx) rs rm,
        bridge_equiv (sys.bridge a) rs rm)
    (a b : sys.ActionIdx)
    (hb_fails : ¬ bridge_equiv (sys.bridge b)
        (sys.step_sut b (sys.step_sut a ss).1).2
        (sys.step_model b (sys.step_model a sm).1).2) :
    bounded_bisim sys 1 sm ss ∧ ¬ bounded_bisim sys 2 sm ss :=
  opaque_depth_sensitivity sys sm ss hall_opaque a b hb_fails

/--
  **General tight bound**: failure at successor depth k implies
  failure at original depth k+1. This is the exact relationship —
  the detection depth is 1 + the successor failure depth.
-/
theorem detection_depth_exact (sys : LockstepSystem)
    (sm : sys.SM) (ss : sys.SS)
    (a : sys.ActionIdx) (k : Nat)
    (hfail : ¬ bounded_bisim sys k
        (sys.step_model a sm).1 (sys.step_sut a ss).1) :
    ¬ bounded_bisim sys (k + 1) sm ss :=
  detection_at_successor sys sm ss a k hfail

/--
  **Depth chain**: bridge failure at action b after action a gives
  both depth-1 failure at successor AND depth-2 failure at start.
-/
theorem depth_chain_2 (sys : LockstepSystem)
    (sm : sys.SM) (ss : sys.SS)
    (a b : sys.ActionIdx)
    (hb_fails : ¬ bridge_equiv (sys.bridge b)
        (sys.step_sut b (sys.step_sut a ss).1).2
        (sys.step_model b (sys.step_model a sm).1).2) :
    ¬ bounded_bisim sys 1
        (sys.step_model a sm).1 (sys.step_sut a ss).1
    ∧ ¬ bounded_bisim sys 2 sm ss := by
  exact ⟨immediate_bug sys _ _ b hb_fails,
         detection_at_successor sys sm ss a 1
           (immediate_bug sys _ _ b hb_fails)⟩

/--
  **Failure is monotone**: failure at depth n implies failure at
  all depths m ≥ n. Once we know the minimum depth, all deeper
  tests also detect the failure.
-/
theorem failure_monotone (sys : LockstepSystem)
    (n m : Nat) (hle : n ≤ m)
    (sm : sys.SM) (ss : sys.SS)
    (hfail : ¬ bounded_bisim sys n sm ss) :
    ¬ bounded_bisim sys m sm ss :=
  failure_propagates_up sys sm ss n m hle hfail
