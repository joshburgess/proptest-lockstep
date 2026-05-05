/-
  Derived Bridge Monotonicity

  Proves that the polynomial bridge derivation is monotone in
  refinement: replacing a component bridge with a finer one produces
  a finer composite bridge. This is the key property for the proc
  macro's `derive_bridge` function -- users control observation
  precision by choosing transparent vs opaque at each leaf, and
  composition preserves the refinement ordering.

  Note: The individual lift preservation theorems (each derivation
  step preserves bridge_equiv) are proved in Bridge.lean as the
  fundamental theorem. This file focuses on the refinement-ordering
  properties that are specific to the derivation story.
-/

import Metatheory.BridgeRefinement

-- =========================================================================
-- Derivation is monotone in refinement
-- =========================================================================

/--
  **Sum derivation is monotone**: replacing component bridges with
  finer ones produces a finer sum bridge. For the Ok case.
-/
theorem derivation_monotone_sum_ok
    (bOk1 bOk2 : Bridge ROk MOk) (bErr1 bErr2 : Bridge RErr MErr)
    [DecidableEq bOk1.Observed] [DecidableEq bErr1.Observed]
    [DecidableEq bOk2.Observed] [DecidableEq bErr2.Observed]
    (hOk : bridge_refines bOk1 bOk2)
    (_hErr : bridge_refines bErr1 bErr2)
    (rok : ROk) (mok : MOk)
    (h : bridge_equiv (sumBridge bOk1 bErr1) (.inl rok) (.inl mok)) :
    bridge_equiv (sumBridge bOk2 bErr2) (.inl rok) (.inl mok) := by
  exact sum_preserves_ok bOk2 bErr2 rok mok
    (hOk rok mok (by unfold bridge_equiv sumBridge at h; simp at h; exact h))

/--
  **Sum derivation is monotone**: Err case.
-/
theorem derivation_monotone_sum_err
    (bOk1 bOk2 : Bridge ROk MOk) (bErr1 bErr2 : Bridge RErr MErr)
    [DecidableEq bOk1.Observed] [DecidableEq bErr1.Observed]
    [DecidableEq bOk2.Observed] [DecidableEq bErr2.Observed]
    (_hOk : bridge_refines bOk1 bOk2)
    (hErr : bridge_refines bErr1 bErr2)
    (rerr : RErr) (merr : MErr)
    (h : bridge_equiv (sumBridge bOk1 bErr1) (.inr rerr) (.inr merr)) :
    bridge_equiv (sumBridge bOk2 bErr2) (.inr rerr) (.inr merr) := by
  exact sum_preserves_err bOk2 bErr2 rerr merr
    (hErr rerr merr (by unfold bridge_equiv sumBridge at h; simp at h; exact h))

/--
  **Product derivation is monotone**: replacing component bridges with
  finer ones produces a finer product bridge.
-/
theorem derivation_monotone_prod
    (bA1 bA2 : Bridge RA MA) (bB1 bB2 : Bridge RB MB)
    [DecidableEq bA1.Observed] [DecidableEq bB1.Observed]
    [DecidableEq bA2.Observed] [DecidableEq bB2.Observed]
    (hA : bridge_refines bA1 bA2) (hB : bridge_refines bB1 bB2)
    (ra : RA) (ma : MA) (rb : RB) (mb : MB)
    (h : bridge_equiv (prodBridge bA1 bB1) (ra, rb) (ma, mb)) :
    bridge_equiv (prodBridge bA2 bB2) (ra, rb) (ma, mb) := by
  rw [prod_equiv_iff] at h
  exact prod_preserves bA2 bB2 ra ma rb mb (hA ra ma h.1) (hB rb mb h.2)

/--
  **Option derivation is monotone**: replacing the inner bridge with
  a finer one produces a finer option bridge.
-/
theorem derivation_monotone_option
    (b1 b2 : Bridge R M)
    [DecidableEq b1.Observed] [DecidableEq b2.Observed]
    (h : bridge_refines b1 b2)
    (r : R) (m : M)
    (hequiv : bridge_equiv (optionBridge b1) (some r) (some m)) :
    bridge_equiv (optionBridge b2) (some r) (some m) := by
  unfold bridge_equiv optionBridge at hequiv ⊢
  simp at hequiv ⊢
  exact h r m hequiv

/--
  **List derivation is monotone**: replacing the inner bridge with
  a finer one produces a finer list bridge.
-/
theorem derivation_monotone_list
    (b1 b2 : Bridge R M)
    [DecidableEq b1.Observed] [DecidableEq b2.Observed]
    (h : bridge_refines b1 b2)
    (rs : List R) (ms : List M)
    (hequiv : bridge_equiv (listBridge b1) rs ms) :
    bridge_equiv (listBridge b2) rs ms :=
  list_refines b1 b2 h rs ms hequiv
