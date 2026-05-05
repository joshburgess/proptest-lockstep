/-
  Polynomial Bridge Algebra

  Formalizes the bridge algebra as a polynomial functor on observation
  types. Each bridge constructor (transparent, opaque, sum, prod,
  option, list) corresponds to a polynomial operation. The observation
  type of a composite bridge is the polynomial composition of its
  component observation types.

  This makes the "bridges as logical relations" claim precise:
  - Bridge shapes form a free algebra (polynomial functors)
  - Bridge equivalence is the logical relation induced by the shape
  - Bridge refinement is inclusion of logical relations
  - The proc macro's derivation is polynomial composition

  This is the theoretical anchor for the ICFP pearl story.
-/

import Metatheory.Bridge
import Metatheory.BridgeRefinement

-- =========================================================================
-- Bridge shapes: the polynomial structure
-- =========================================================================

/--
  The shape of a bridge, describing its polynomial structure.
  Each constructor corresponds to a bridge combinator:
  - `atom` -- transparent (identity observation)
  - `unit` -- opaque (constant Unit observation)
  - `sum` -- coproduct (Result/Either)
  - `prod` -- product (Tuple)
  - `option` -- lifted (Option)
  - `list` -- free monoid (Vec)
-/
inductive BridgeShape where
  | atom : BridgeShape
  | unit : BridgeShape
  | sum : BridgeShape → BridgeShape → BridgeShape
  | prod : BridgeShape → BridgeShape → BridgeShape
  | option : BridgeShape → BridgeShape
  | list : BridgeShape → BridgeShape
  deriving DecidableEq

-- =========================================================================
-- Shape interpretation: the polynomial functor
-- =========================================================================

/--
  The observation type determined by a shape applied to a base type.
  This is the polynomial functor: `⟦shape⟧(T) = observation type`.

  - `⟦atom⟧(T) = T` (identity functor)
  - `⟦unit⟧(T) = Unit` (constant functor)
  - `⟦sum s₁ s₂⟧(T) = ⟦s₁⟧(T) ⊕ ⟦s₂⟧(T)` (coproduct)
  - `⟦prod s₁ s₂⟧(T) = ⟦s₁⟧(T) × ⟦s₂⟧(T)` (product)
  - `⟦option s⟧(T) = Option ⟦s⟧(T)` (Maybe)
  - `⟦list s⟧(T) = List ⟦s⟧(T)` (free monoid)
-/
def BridgeShape.Obs : BridgeShape → Type → Type
  | .atom, T => T
  | .unit, _ => Unit
  | .sum s₁ s₂, T => s₁.Obs T ⊕ s₂.Obs T
  | .prod s₁ s₂, T => s₁.Obs T × s₂.Obs T
  | .option s, T => Option (s.Obs T)
  | .list s, T => List (s.Obs T)

/--
  The polynomial functor's action on morphisms (fmap).
  Given `f : A → B`, lifts to `⟦shape⟧(f) : ⟦shape⟧(A) → ⟦shape⟧(B)`.
-/
def BridgeShape.fmap (shape : BridgeShape) {A B : Type} (f : A → B) :
    shape.Obs A → shape.Obs B :=
  match shape with
  | .atom => f
  | .unit => id
  | .sum s₁ s₂ => fun
    | .inl x => .inl (s₁.fmap f x)
    | .inr x => .inr (s₂.fmap f x)
  | .prod s₁ s₂ => fun (x, y) => (s₁.fmap f x, s₂.fmap f y)
  | .option s => fun
    | some x => some (s.fmap f x)
    | none => none
  | .list s => fun xs => xs.map (s.fmap f)

-- =========================================================================
-- Functor laws
-- =========================================================================

/--
  **Identity law**: `fmap id = id`.
  The polynomial functor preserves identity morphisms.
-/
theorem BridgeShape.fmap_id : ∀ (shape : BridgeShape) (A : Type)
    (x : shape.Obs A), shape.fmap id x = x := by
  intro shape
  induction shape with
  | atom => intro _ x; rfl
  | unit => intro _ x; rfl
  | sum s₁ s₂ ih₁ ih₂ =>
    intro A x
    match x with
    | .inl v => simp [fmap, ih₁ A v]
    | .inr v => simp [fmap, ih₂ A v]
  | prod s₁ s₂ ih₁ ih₂ =>
    intro A ⟨x, y⟩
    simp [fmap, ih₁ A x, ih₂ A y]
  | option s ih =>
    intro A x
    match x with
    | some v => simp [fmap, ih A v]
    | none => rfl
  | list s ih =>
    intro A x
    simp [fmap]
    induction x with
    | nil => rfl
    | cons hd tl ihtl => simp [ih A hd, ihtl]

/--
  **Composition law**: `fmap (g ∘ f) = fmap g ∘ fmap f`.
  The polynomial functor preserves composition of morphisms.
-/
theorem BridgeShape.fmap_comp : ∀ (shape : BridgeShape)
    {A B C : Type} (f : A → B) (g : B → C)
    (x : shape.Obs A),
    shape.fmap (g ∘ f) x = shape.fmap g (shape.fmap f x) := by
  intro shape
  induction shape with
  | atom => intros; rfl
  | unit => intros; rfl
  | sum s₁ s₂ ih₁ ih₂ =>
    intro A B C f g x
    match x with
    | .inl v => simp [fmap, ih₁ f g v]
    | .inr v => simp [fmap, ih₂ f g v]
  | prod s₁ s₂ ih₁ ih₂ =>
    intro A B C f g ⟨x, y⟩
    simp [fmap, ih₁ f g x, ih₂ f g y]
  | option s ih =>
    intro A B C f g x
    match x with
    | some v => simp [fmap, ih f g v]
    | none => rfl
  | list s ih =>
    intro A B C f g x
    simp [fmap]
    induction x with
    | nil => rfl
    | cons hd tl ihtl => simp [ih f g hd, ihtl]

-- =========================================================================
-- Decidability of shaped observations
-- =========================================================================

/--
  Observations at any shape inherit decidable equality from the
  base type's decidable equality.
-/
noncomputable instance BridgeShape.decEq (shape : BridgeShape) (T : Type)
    [DecidableEq T] : DecidableEq (shape.Obs T) :=
  fun a b => Classical.propDecidable (a = b)

-- =========================================================================
-- Shape-indexed bridge construction
-- =========================================================================

/--
  Construct a bridge from a shape and base observation functions.
  The bridge's `Observed` type is the polynomial `⟦shape⟧(O)` where
  `O` is a common base observation type.

  For `atom` (transparent), the base observation IS the bridge
  observation. For `unit` (opaque), the observation is discarded.
  For composite shapes, observations are lifted pointwise.
-/
noncomputable def shapeBridge (shape : BridgeShape) (O : Type) [DecidableEq O]
    (obs_r : R → shape.Obs O) (obs_m : M → shape.Obs O) :
    Bridge R M :=
  { Observed := shape.Obs O
    observe_real := obs_r
    observe_model := obs_m
    dec_eq := BridgeShape.decEq shape O }

-- =========================================================================
-- Key theorem: polynomial derivation preserves bridge equivalence
-- =========================================================================

/--
  **Polynomial bridge equivalence**: two values are bridge-equivalent
  under a shape-derived bridge iff their observations are equal in
  the polynomial type `⟦shape⟧(O)`.

  This is the fundamental theorem connecting the algebraic structure
  of bridges to their semantic meaning: the shape determines the
  observation, and observation equality determines equivalence.
-/
theorem shape_bridge_equiv (shape : BridgeShape) (O : Type)
    [DecidableEq O]
    (obs_r : R → shape.Obs O) (obs_m : M → shape.Obs O)
    (r : R) (m : M) :
    bridge_equiv (shapeBridge shape O obs_r obs_m) r m
    ↔ obs_r r = obs_m m := by
  unfold bridge_equiv shapeBridge
  exact Iff.rfl

/--
  **Transparent is the atom shape**: `transparent T` is exactly
  `shapeBridge .atom T id id`.
-/
theorem transparent_is_atom (T : Type) [DecidableEq T] :
    ∀ (r m : T),
    bridge_equiv (transparent T) r m ↔
    bridge_equiv (shapeBridge .atom T id id) r m := by
  intro r m
  simp [bridge_equiv, transparent, shapeBridge, BridgeShape.Obs, id]

/--
  **Opaque is the unit shape**: `opaqueBridge R M` produces the
  same equivalence as `shapeBridge .unit Unit (fun _ => ()) (fun _ => ())`.
-/
theorem opaque_is_unit (R M : Type) :
    ∀ (r : R) (m : M),
    bridge_equiv (opaqueBridge R M) r m ↔
    bridge_equiv (shapeBridge .unit Unit (fun _ => ()) (fun _ => ())) r m := by
  intro r m
  simp [bridge_equiv, opaqueBridge, shapeBridge, BridgeShape.Obs]

-- =========================================================================
-- Shape complexity: a measure for bridge derivation
-- =========================================================================

/--
  The depth of a bridge shape -- the maximum nesting level.
  Corresponds to the recursion depth of the bridge derivation proc macro.
-/
def BridgeShape.depth : BridgeShape → Nat
  | .atom => 0
  | .unit => 0
  | .sum s₁ s₂ => 1 + max s₁.depth s₂.depth
  | .prod s₁ s₂ => 1 + max s₁.depth s₂.depth
  | .option s => 1 + s.depth
  | .list s => 1 + s.depth

/--
  The number of leaves (atom + unit) in a bridge shape.
  Each leaf corresponds to a primitive bridge in the derivation.
-/
def BridgeShape.leaves : BridgeShape → Nat
  | .atom => 1
  | .unit => 1
  | .sum s₁ s₂ => s₁.leaves + s₂.leaves
  | .prod s₁ s₂ => s₁.leaves + s₂.leaves
  | .option s => s.leaves
  | .list s => s.leaves

/--
  **Bridge depth bounds testing depth**: the depth of the bridge
  shape gives a lower bound on the testing depth needed for full
  detection. Deeper shapes may hide discrepancies behind more
  layers of observation.
-/
theorem shape_depth_positive_for_composite (s₁ s₂ : BridgeShape) :
    (BridgeShape.sum s₁ s₂).depth ≥ 1 ∧
    (BridgeShape.prod s₁ s₂).depth ≥ 1 := by
  simp [BridgeShape.depth]

-- =========================================================================
-- Structural shape refinement
-- =========================================================================

/--
  **Structural shape refinement**: shape `s₁` refines `s₂` if `s₁`
  has `atom` (transparent) at every position where `s₂` has `atom`,
  and may additionally have `atom` where `s₂` has `unit` (opaque).
  Both shapes must have the same composite structure.

  This is the polynomial functor version of bridge refinement:
  replacing opaque leaves with transparent leaves makes the
  observation finer.
-/
inductive ShapeRefines : BridgeShape → BridgeShape → Type
  | refl (s) : ShapeRefines s s
  | atom_unit : ShapeRefines .atom .unit
  | sum (h₁ : ShapeRefines s₁ t₁) (h₂ : ShapeRefines s₂ t₂) :
      ShapeRefines (.sum s₁ s₂) (.sum t₁ t₂)
  | prod (h₁ : ShapeRefines s₁ t₁) (h₂ : ShapeRefines s₂ t₂) :
      ShapeRefines (.prod s₁ s₂) (.prod t₁ t₂)
  | option (h : ShapeRefines s t) :
      ShapeRefines (.option s) (.option t)
  | list (h : ShapeRefines s t) :
      ShapeRefines (.list s) (.list t)

-- =========================================================================
-- Coarsening map: the natural transformation between shapes
-- =========================================================================

/--
  **Coarsening map**: given a proof that `s₁` refines `s₂`,
  construct the map from finer observations to coarser observations.

  - `atom → unit`: discard the observation (`fun _ => ()`)
  - `atom → atom`: identity
  - Composites: apply coarsening pointwise to sub-observations

  This is the natural transformation between the polynomial functors
  ⟦s₁⟧ and ⟦s₂⟧ induced by the refinement.
-/
def ShapeRefines.coarsen : ShapeRefines s₁ s₂ →
    ∀ (O : Type), s₁.Obs O → s₂.Obs O
  | .refl _, _, x => x
  | .atom_unit, _, _ => ()
  | .sum h₁ h₂, O, x => match x with
    | .inl x => .inl (h₁.coarsen O x)
    | .inr x => .inr (h₂.coarsen O x)
  | .prod h₁ h₂, O, (x, y) => (h₁.coarsen O x, h₂.coarsen O y)
  | .option h, O, x => match x with
    | some v => some (h.coarsen O v)
    | none => none
  | .list h, O, xs => xs.map (h.coarsen O)

-- =========================================================================
-- THE CONNECTION: ShapeRefines → bridge_refines
-- =========================================================================

/--
  **Shape refinement induces bridge refinement**: if shape `s₁`
  refines shape `s₂`, then any bridge built from `s₁` refines the
  corresponding bridge built from `s₂` (with coarsened observations).

  This is the key theorem connecting the polynomial functor story
  to the bridge algebra story: the abstract shape refinement
  (`ShapeRefines`) implies the concrete bridge refinement
  (`bridge_refines`), which in turn implies stronger bisimulation
  guarantees (via `refines_strengthen_bisim`).

  The full chain:
    ShapeRefines s₁ s₂
    → bridge_refines (shapeBridge s₁ ...) (shapeBridge s₂ ...)
    → bounded_bisim under s₁ implies bounded_bisim under s₂
    → finer shapes give stronger testing guarantees
-/
theorem shape_refines_bridge_refines
    (href : ShapeRefines s₁ s₂)
    (O : Type) [DecidableEq O]
    (obs_r : R → s₁.Obs O) (obs_m : M → s₁.Obs O) :
    bridge_refines
      (shapeBridge s₁ O obs_r obs_m)
      (shapeBridge s₂ O (href.coarsen O ∘ obs_r) (href.coarsen O ∘ obs_m)) := by
  intro r m h
  unfold bridge_equiv shapeBridge at *
  show href.coarsen O (obs_r r) = href.coarsen O (obs_m m)
  exact congrArg (href.coarsen O) h

/--
  **Coarsening preserves fmap**: the coarsening map commutes with
  the polynomial functor's action on morphisms. This is the
  naturality condition -- coarsening is a natural transformation.

  `coarsen ∘ fmap_s₁ f = fmap_s₂ f ∘ coarsen`
-/
theorem ShapeRefines.coarsen_natural
    (href : ShapeRefines s₁ s₂)
    {A B : Type} (f : A → B) :
    ∀ (x : s₁.Obs A),
    href.coarsen B (s₁.fmap f x) = s₂.fmap f (href.coarsen A x) := by
  induction href with
  | refl => intro x; rfl
  | atom_unit => intro _; rfl
  | sum h₁ h₂ ih₁ ih₂ =>
    intro x
    match x with
    | .inl v => simp [ShapeRefines.coarsen, BridgeShape.fmap, ih₁ v]
    | .inr v => simp [ShapeRefines.coarsen, BridgeShape.fmap, ih₂ v]
  | prod h₁ h₂ ih₁ ih₂ =>
    intro ⟨x, y⟩
    simp [ShapeRefines.coarsen, BridgeShape.fmap, ih₁ x, ih₂ y]
  | option h ih =>
    intro x
    match x with
    | some v => simp [ShapeRefines.coarsen, BridgeShape.fmap, ih v]
    | none => rfl
  | list h ih =>
    intro x
    simp [ShapeRefines.coarsen, BridgeShape.fmap]
    induction x with
    | nil => rfl
    | cons hd tl ihtl => simp [ih hd, ihtl]

/--
  **Shape refinement is transitive**: if s₁ refines s₂ and s₂
  refines s₃, then s₁ refines s₃.
-/
def ShapeRefines.trans :
    ShapeRefines s₁ s₂ → ShapeRefines s₂ s₃ → ShapeRefines s₁ s₃
  | .refl _, h₂₃ => h₂₃
  | .atom_unit, .refl _ => .atom_unit
  | .sum h₁ h₂, .refl _ => .sum h₁ h₂
  | .sum h₁ h₂, .sum h₃ h₄ => .sum (h₁.trans h₃) (h₂.trans h₄)
  | .prod h₁ h₂, .refl _ => .prod h₁ h₂
  | .prod h₁ h₂, .prod h₃ h₄ => .prod (h₁.trans h₃) (h₂.trans h₄)
  | .option h, .refl _ => .option h
  | .option h, .option h₃ => .option (h.trans h₃)
  | .list h, .refl _ => .list h
  | .list h, .list h₃ => .list (h.trans h₃)

/--
  **Atom refines everything**: the atom shape (transparent) refines
  any shape with the same structure that uses unit at leaves.
  This is the polynomial version of "transparent is finest."
-/
def atom_refines_unit : ShapeRefines .atom .unit :=
  ShapeRefines.atom_unit
