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
