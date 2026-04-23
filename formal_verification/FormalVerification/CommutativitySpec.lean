/-
  Commutativity Specification Testing

  Formalizes commutativity specification testing: given a predicate
  `should_commute` declaring which action pairs should commute, the
  framework tests whether the model actually satisfies the spec.

  A commutativity specification is SOUND if `should_commute(a, b, sm)`
  implies `model_commute a b sm` (the actions actually commute).
  A violation is when the spec says "commute" but the model disagrees.

  Key result: if the commutativity spec is sound, then DPOR using the
  spec as its oracle is also sound -- connecting commutativity specs
  to the existing DPOR soundness formalization.

  Corresponds to `CommutativitySpecModel` in `src/commutativity.rs`.
-/

import FormalVerification.DPOR
import FormalVerification.Invariant

-- =========================================================================
-- Commutativity specification
-- =========================================================================

/--
  A lockstep system extended with a commutativity specification.
  The spec declares which pairs of actions should commute at a
  given model state.
-/
structure CommutativitySpecSystem extends LockstepSystem where
  should_commute : ActionIdx → ActionIdx → SM → Prop

/--
  A commutativity specification is SOUND if whenever the spec says
  two actions commute, they actually do (in the model_commute sense).
-/
def spec_sound (sys : CommutativitySpecSystem) : Prop :=
  ∀ (a b : sys.ActionIdx) (sm : sys.SM),
    sys.should_commute a b sm →
    model_commute sys.toLockstepSystem a b sm

-- =========================================================================
-- Spec soundness implies DPOR soundness
-- =========================================================================

/--
  **Spec-guided DPOR is sound**: if the commutativity spec is sound,
  then using the spec as the DPOR oracle preserves linearization
  validity. This connects commutativity specs to the existing DPOR
  soundness proof.
-/
theorem spec_dpor_sound (sys : CommutativitySpecSystem)
    (hsound : spec_sound sys)
    (r1 r2 : OpRecord sys.toLockstepSystem)
    (rest : List (OpRecord sys.toLockstepSystem))
    (sm : sys.SM)
    (hspec : sys.should_commute r1.action r2.action sm)
    (h : linearization_check sys.toLockstepSystem (r1 :: r2 :: rest) sm) :
    linearization_check sys.toLockstepSystem (r2 :: r1 :: rest) sm :=
  dpor_swap_sound sys.toLockstepSystem r1 r2 rest sm
    (hsound r1.action r2.action sm hspec) h

-- =========================================================================
-- Spec violation detection
-- =========================================================================

/--
  A commutativity spec violation: the spec says the actions should
  commute, but they don't. This is the formal statement of what
  the `run_commutativity_test` runner checks.
-/
def spec_violation (sys : CommutativitySpecSystem)
    (a b : sys.ActionIdx) (sm : sys.SM) : Prop :=
  sys.should_commute a b sm ∧ ¬ model_commute sys.toLockstepSystem a b sm

/--
  **No violations iff spec is sound**: the spec is sound exactly
  when there are no violations.
-/
theorem sound_iff_no_violations (sys : CommutativitySpecSystem) :
    spec_sound sys ↔
    ∀ (a b : sys.ActionIdx) (sm : sys.SM),
      ¬ spec_violation sys a b sm := by
  constructor
  · intro hsound a b sm ⟨hspec, hnotcomm⟩
    exact hnotcomm (hsound a b sm hspec)
  · intro hnoviols a b sm hspec
    exact Classical.byContradiction (fun hnotcomm =>
      hnoviols a b sm ⟨hspec, hnotcomm⟩)

-- =========================================================================
-- Symmetry
-- =========================================================================

/--
  **Sound spec implies reversed commutativity**: if the spec is
  sound (should_commute → model_commute), then should_commute also
  implies model_commute in the reversed order (via `commute_sym`).
-/
theorem symmetric_spec_sound (sys : CommutativitySpecSystem)
    (hsound : spec_sound sys) :
    ∀ (a b : sys.ActionIdx) (sm : sys.SM),
      sys.should_commute a b sm →
      model_commute sys.toLockstepSystem b a sm :=
  fun a b sm hspec =>
    commute_sym sys.toLockstepSystem a b sm (hsound a b sm hspec)

-- =========================================================================
-- Spec refinement
-- =========================================================================

/--
  **Spec refinement**: given the same lockstep system, a finer spec
  (one that claims fewer things commute) is easier to satisfy. If a
  coarser spec is sound, any finer spec is also sound.
-/
theorem finer_spec_sound (sys : LockstepSystem)
    (spec1 spec2 : sys.ActionIdx → sys.ActionIdx → sys.SM → Prop)
    (hfiner : ∀ a b sm, spec1 a b sm → spec2 a b sm)
    (hsound2 : ∀ a b sm, spec2 a b sm → model_commute sys a b sm) :
    ∀ a b sm, spec1 a b sm → model_commute sys a b sm :=
  fun a b sm hspec => hsound2 a b sm (hfiner a b sm hspec)
