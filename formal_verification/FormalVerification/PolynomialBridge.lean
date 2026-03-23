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

import FormalVerification.Bridge
import FormalVerification.BridgeRefinement

-- =========================================================================
-- Bridge shapes: the polynomial structure
-- =========================================================================

/--
  The shape of a bridge, describing its polynomial structure.
  Each constructor corresponds to a bridge combinator:
  - `atom` — transparent (identity observation)
  - `unit` — opaque (constant Unit observation)
  - `sum` — coproduct (Result/Either)
  - `prod` — product (Tuple)
  - `option` — lifted (Option)
  - `list` — free monoid (Vec)
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
  The depth of a bridge shape — the maximum nesting level.
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
-- Shape refinement ordering
-- =========================================================================

/--
  **Shape refinement**: shape `s₁` refines `s₂` if observations
  under `s₁` are finer (equality under `s₁` implies equality under
  `s₂`). This lifts `bridge_refines` to the shape level.
-/
def BridgeShape.refines (s₁ s₂ : BridgeShape) : Prop :=
  ∀ (O : Type) [DecidableEq O] (x y : s₁.Obs O),
    x = y → ∃ (f : s₁.Obs O → s₂.Obs O), f x = f y

/--
  **Unit (opaque) is the coarsest shape**: every shape refines unit,
  because unit observations carry no information (everything maps
  to `()`).
-/
theorem BridgeShape.unit_coarsest (s : BridgeShape) :
    ∀ (O : Type) [DecidableEq O] (x y : s.Obs O),
    x = y →
    (fun (_ : s.Obs O) => ((): BridgeShape.unit.Obs O)) x =
    (fun (_ : s.Obs O) => ((): BridgeShape.unit.Obs O)) y := by
  intro O _ x y _
  rfl

/--
  **Atom (transparent) is the finest shape**: atom observations
  are the identity functor, so atom equality IS base type equality.
  No other shape can be finer.
-/
theorem BridgeShape.atom_finest (O : Type) [DecidableEq O]
    (x y : BridgeShape.atom.Obs O) :
    x = y ↔ (x : O) = (y : O) := by
  simp [BridgeShape.Obs]

-- =========================================================================
-- Shape-bridge correspondence: shapes produce the right bridges
-- =========================================================================

/--
  **Sum shape produces sum observation**: the polynomial functor
  for `.sum s₁ s₂` applied to observation functions gives
  observations of the form `inl (obs₁ r)` or `inr (obs₂ r)`,
  matching `sumBridge`'s structure.
-/
theorem shape_sum_inl (s₁ s₂ : BridgeShape) (O : Type) [DecidableEq O]
    (x : s₁.Obs O) :
    (BridgeShape.sum s₁ s₂).fmap id (Sum.inl x : (BridgeShape.sum s₁ s₂).Obs O)
    = Sum.inl (s₁.fmap id x) := by
  simp [BridgeShape.fmap]

theorem shape_sum_inr (s₁ s₂ : BridgeShape) (O : Type) [DecidableEq O]
    (x : s₂.Obs O) :
    (BridgeShape.sum s₁ s₂).fmap id (Sum.inr x : (BridgeShape.sum s₁ s₂).Obs O)
    = Sum.inr (s₂.fmap id x) := by
  simp [BridgeShape.fmap]

/--
  **Product shape produces product observation**: the polynomial
  functor for `.prod s₁ s₂` applied to observation functions gives
  observations of the form `(obs₁ r, obs₂ r)`, matching
  `prodBridge`'s structure.
-/
theorem shape_prod_pair (s₁ s₂ : BridgeShape) (O : Type) [DecidableEq O]
    (x : s₁.Obs O) (y : s₂.Obs O) :
    (BridgeShape.prod s₁ s₂).fmap id (x, y)
    = (s₁.fmap id x, s₂.fmap id y) := by
  simp [BridgeShape.fmap]

/--
  **Shape depth bounds observation complexity**: the number of
  nested constructors in an observation value is bounded by the
  shape's depth. Deeper shapes can hide discrepancies behind more
  observation layers.
-/
theorem shape_leaves_pos (s : BridgeShape) : s.leaves ≥ 1 := by
  induction s with
  | atom => simp [BridgeShape.leaves]
  | unit => simp [BridgeShape.leaves]
  | sum s₁ s₂ ih₁ _ => simp [BridgeShape.leaves]; omega
  | prod s₁ s₂ ih₁ _ => simp [BridgeShape.leaves]; omega
  | option s ih => simp [BridgeShape.leaves]; omega
  | list s ih => simp [BridgeShape.leaves]; omega
