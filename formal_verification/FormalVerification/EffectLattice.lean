/-
  Effect-Indexed Commutativity Lattice

  Formalizes the static effect annotation system for O(1) commutativity
  checking. An effect algebra provides a `conflicts` predicate; two
  actions commute iff their effects don't conflict.

  The key result: if the effect algebra is SOUND (effects that don't
  conflict imply model commutativity), then using effects for DPOR
  is sound — connecting static effect annotations to the existing
  DPOR soundness proof.

  Corresponds to `EffectModel` and `ConflictAlgebra` in `src/effects.rs`.
-/

import FormalVerification.DPOR

-- =========================================================================
-- Effect algebra
-- =========================================================================

/--
  An effect algebra: a type with a conflict relation that determines
  commutativity. Two effects conflict iff the operations they
  represent don't commute.
-/
structure EffectAlgebra where
  Effect : Type
  conflicts : Effect → Effect → Prop

/-- Two effects commute iff they don't conflict. -/
def EffectAlgebra.commutes (ea : EffectAlgebra) (e1 e2 : ea.Effect) : Prop :=
  ¬ ea.conflicts e1 e2

-- =========================================================================
-- Effect-annotated system
-- =========================================================================

/--
  A lockstep system extended with effect annotations.
  Each action has an effect, and commutativity is determined by
  whether effects conflict.
-/
structure EffectSystem extends LockstepSystem where
  algebra : EffectAlgebra
  effect_of : ActionIdx → algebra.Effect

/--
  The effect annotation is SOUND if non-conflicting effects imply
  model commutativity. This ensures that using effects for DPOR
  is safe — we never skip an interleaving that should be explored.
-/
def effect_sound (sys : EffectSystem) : Prop :=
  ∀ (a b : sys.ActionIdx) (sm : sys.SM),
    sys.algebra.commutes (sys.effect_of a) (sys.effect_of b) →
    model_commute sys.toLockstepSystem a b sm

-- =========================================================================
-- Effect soundness implies DPOR soundness
-- =========================================================================

/--
  **Effect-guided DPOR is sound**: if the effect annotations are
  sound, then using effects for commutativity detection preserves
  linearization validity. This connects static effect annotations
  to the existing `dpor_swap_sound` proof.
-/
theorem effect_dpor_sound (sys : EffectSystem)
    (hsound : effect_sound sys)
    (r1 r2 : OpRecord sys.toLockstepSystem)
    (rest : List (OpRecord sys.toLockstepSystem))
    (sm : sys.SM)
    (heffect : sys.algebra.commutes (sys.effect_of r1.action) (sys.effect_of r2.action))
    (h : linearization_check sys.toLockstepSystem (r1 :: r2 :: rest) sm) :
    linearization_check sys.toLockstepSystem (r2 :: r1 :: rest) sm :=
  dpor_swap_sound sys.toLockstepSystem r1 r2 rest sm
    (hsound r1.action r2.action sm heffect) h

-- =========================================================================
-- Properties of effect algebras
-- =========================================================================

/--
  A symmetric effect algebra: conflict is symmetric.
  Most natural conflict relations are symmetric (if A conflicts
  with B, then B conflicts with A).
-/
def effect_symmetric (ea : EffectAlgebra) : Prop :=
  ∀ (e1 e2 : ea.Effect), ea.conflicts e1 e2 → ea.conflicts e2 e1

/--
  **Symmetric effects give symmetric commutativity**: if the conflict
  relation is symmetric, then commutativity derived from effects is
  also symmetric.
-/
theorem symmetric_commutes (ea : EffectAlgebra) (hsym : effect_symmetric ea)
    (e1 e2 : ea.Effect) (h : ea.commutes e1 e2) :
    ea.commutes e2 e1 := by
  unfold EffectAlgebra.commutes at h ⊢
  intro hconf
  exact h (hsym e2 e1 hconf)

/--
  **Soundness composition**: if effect annotations are sound for
  system `sys`, and we refine the effect algebra to be more
  conservative (more conflicts), the annotations remain sound.
-/
theorem conservative_effects_sound (sys : EffectSystem)
    (conflicts' : sys.algebra.Effect → sys.algebra.Effect → Prop)
    (hmore : ∀ e1 e2, sys.algebra.conflicts e1 e2 → conflicts' e1 e2)
    (hsound : effect_sound sys) :
    -- The new algebra with more conflicts is also sound
    ∀ (a b : sys.ActionIdx) (sm : sys.SM),
      ¬ conflicts' (sys.effect_of a) (sys.effect_of b) →
      model_commute sys.toLockstepSystem a b sm := by
  intro a b sm hnoconf
  apply hsound a b sm
  unfold EffectAlgebra.commutes
  intro hconf
  exact hnoconf (hmore _ _ hconf)

-- =========================================================================
-- Read/Write effect algebra
-- =========================================================================

/--
  The standard read/write effect: an operation either reads or writes
  a resource. This is the most common effect pattern.
-/
inductive RWEffect (Resource : Type)
  | read : Resource → RWEffect Resource
  | write : Resource → RWEffect Resource
  | readAll : RWEffect Resource
  | writeAll : RWEffect Resource
  | none : RWEffect Resource

/--
  The standard read/write conflict relation:
  - Read/Read never conflicts
  - Read/Write on same resource conflicts
  - Write/Write on same resource conflicts
  - WriteAll conflicts with everything except None
-/
def rw_conflicts [DecidableEq R] : RWEffect R → RWEffect R → Prop
  | .none, _ => False
  | _, .none => False
  | .read _, .read _ => False
  | .read _, .readAll => False
  | .readAll, .read _ => False
  | .readAll, .readAll => False
  | .read r1, .write r2 => r1 = r2
  | .write r1, .read r2 => r1 = r2
  | .write r1, .write r2 => r1 = r2
  | .readAll, .write _ => True
  | .write _, .readAll => True
  | .readAll, .writeAll => True
  | .writeAll, .readAll => True
  | .writeAll, _ => True
  | _, .writeAll => True

/--
  The read/write conflict relation is symmetric.
-/
theorem rw_conflicts_symmetric [DecidableEq R] (e1 e2 : RWEffect R) :
    rw_conflicts e1 e2 → rw_conflicts e2 e1 := by
  intro h
  cases e1 <;> cases e2 <;> simp [rw_conflicts] at h ⊢
  all_goals (first | exact h | exact h.symm | trivial)
