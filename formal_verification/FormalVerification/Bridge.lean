/-
  Bridge Algebra as a Logical Relation

  A bridge relates a Real type and a Model type through a common
  Observed type. This is a logical relation in the sense of Reynolds
  (1983): a type-indexed family of relations that is preserved by
  type constructors.
-/

-- A bridge relates Real and Model types through observation.
structure Bridge (R : Type) (M : Type) where
  Observed : Type
  observe_real : R → Observed
  observe_model : M → Observed
  dec_eq : DecidableEq Observed

-- Two values are bridge-equivalent iff their observations are equal.
def bridge_equiv (b : Bridge R M) (r : R) (m : M) : Prop :=
  b.observe_real r = b.observe_model m

-- =========================================================================
-- Primitive bridges
-- =========================================================================

-- Transparent: Real = Model = Observed, identity observation.
def transparent (T : Type) [DecidableEq T] : Bridge T T :=
  { Observed := T
    observe_real := id
    observe_model := id
    dec_eq := inferInstance }

-- Opaque: observation is Unit, always equivalent.
def opaqueBridge (R M : Type) : Bridge R M :=
  { Observed := Unit
    observe_real := fun _ => ()
    observe_model := fun _ => ()
    dec_eq := inferInstance }

-- =========================================================================
-- Algebraic lifts
-- =========================================================================

-- Sum bridge (Result/Either)
def sumBridge (bOk : Bridge ROk MOk) (bErr : Bridge RErr MErr)
    [DecidableEq bOk.Observed] [DecidableEq bErr.Observed] :
    Bridge (ROk ⊕ RErr) (MOk ⊕ MErr) :=
  { Observed := bOk.Observed ⊕ bErr.Observed
    observe_real := fun
      | .inl ok => .inl (bOk.observe_real ok)
      | .inr err => .inr (bErr.observe_real err)
    observe_model := fun
      | .inl ok => .inl (bOk.observe_model ok)
      | .inr err => .inr (bErr.observe_model err)
    dec_eq := inferInstance }

-- Product bridge (Tuple)
def prodBridge (bA : Bridge RA MA) (bB : Bridge RB MB)
    [DecidableEq bA.Observed] [DecidableEq bB.Observed] :
    Bridge (RA × RB) (MA × MB) :=
  { Observed := bA.Observed × bB.Observed
    observe_real := fun (a, b) => (bA.observe_real a, bB.observe_real b)
    observe_model := fun (a, b) => (bA.observe_model a, bB.observe_model b)
    dec_eq := inferInstance }

-- Option bridge
def optionBridge (b : Bridge R M) [DecidableEq b.Observed] :
    Bridge (Option R) (Option M) :=
  { Observed := Option b.Observed
    observe_real := fun
      | some r => some (b.observe_real r)
      | none => none
    observe_model := fun
      | some m => some (b.observe_model m)
      | none => none
    dec_eq := inferInstance }

-- =========================================================================
-- The Fundamental Theorem
-- =========================================================================

-- Transparent bridge is reflexive (identity relation)
theorem transparent_refl (T : Type) [DecidableEq T] (x : T) :
    bridge_equiv (transparent T) x x := by
  unfold bridge_equiv transparent
  rfl

-- Opaque bridge is always satisfied (trivial relation)
theorem opaqueBridge_always (R M : Type) (r : R) (m : M) :
    bridge_equiv (opaqueBridge R M) r m := by
  unfold bridge_equiv opaqueBridge
  rfl

-- Sum lift preserves equivalence (Ok case)
theorem sum_preserves_ok (bOk : Bridge ROk MOk) (bErr : Bridge RErr MErr)
    [DecidableEq bOk.Observed] [DecidableEq bErr.Observed]
    (r : ROk) (m : MOk) (h : bridge_equiv bOk r m) :
    bridge_equiv (sumBridge bOk bErr) (.inl r) (.inl m) := by
  unfold bridge_equiv at *
  unfold sumBridge
  simp
  exact h

-- Sum lift preserves equivalence (Err case)
theorem sum_preserves_err (bOk : Bridge ROk MOk) (bErr : Bridge RErr MErr)
    [DecidableEq bOk.Observed] [DecidableEq bErr.Observed]
    (r : RErr) (m : MErr) (h : bridge_equiv bErr r m) :
    bridge_equiv (sumBridge bOk bErr) (.inr r) (.inr m) := by
  unfold bridge_equiv at *
  unfold sumBridge
  simp
  exact h

-- Sum bridge detects variant mismatches (left-right)
theorem sum_variant_mismatch_lr (bOk : Bridge ROk MOk) (bErr : Bridge RErr MErr)
    [DecidableEq bOk.Observed] [DecidableEq bErr.Observed]
    (r : ROk) (m : MErr) :
    ¬ bridge_equiv (sumBridge bOk bErr) (.inl r) (.inr m) := by
  unfold bridge_equiv sumBridge
  simp

-- Sum bridge detects variant mismatches (right-left)
theorem sum_variant_mismatch_rl (bOk : Bridge ROk MOk) (bErr : Bridge RErr MErr)
    [DecidableEq bOk.Observed] [DecidableEq bErr.Observed]
    (r : RErr) (m : MOk) :
    ¬ bridge_equiv (sumBridge bOk bErr) (.inr r) (.inl m) := by
  unfold bridge_equiv sumBridge
  simp

-- Product lift preserves equivalence
theorem prod_preserves (bA : Bridge RA MA) (bB : Bridge RB MB)
    [DecidableEq bA.Observed] [DecidableEq bB.Observed]
    (ra : RA) (ma : MA) (rb : RB) (mb : MB)
    (ha : bridge_equiv bA ra ma) (hb : bridge_equiv bB rb mb) :
    bridge_equiv (prodBridge bA bB) (ra, rb) (ma, mb) := by
  unfold bridge_equiv at *
  unfold prodBridge
  simp
  exact ⟨ha, hb⟩

-- Option lift preserves equivalence (Some case)
theorem option_preserves_some (b : Bridge R M) [DecidableEq b.Observed]
    (r : R) (m : M) (h : bridge_equiv b r m) :
    bridge_equiv (optionBridge b) (some r) (some m) := by
  unfold bridge_equiv at *
  unfold optionBridge
  simp
  exact h

-- Option lift preserves equivalence (None case)
theorem option_preserves_none (b : Bridge R M) [DecidableEq b.Observed] :
    bridge_equiv (optionBridge b) (none : Option R) (none : Option M) := by
  unfold bridge_equiv optionBridge
  simp

-- List bridge (Vec)
def listBridge (b : Bridge R M) [DecidableEq b.Observed] :
    Bridge (List R) (List M) :=
  { Observed := List b.Observed
    observe_real := fun rs => rs.map b.observe_real
    observe_model := fun ms => ms.map b.observe_model
    dec_eq := inferInstance }

-- List lift preserves equivalence (nil case)
theorem list_preserves_nil (b : Bridge R M) [DecidableEq b.Observed] :
    bridge_equiv (listBridge b) ([] : List R) ([] : List M) := by
  unfold bridge_equiv listBridge
  simp

-- List lift preserves equivalence (cons case)
theorem list_preserves_cons (b : Bridge R M) [DecidableEq b.Observed]
    (r : R) (m : M) (rs : List R) (ms : List M)
    (hd : bridge_equiv b r m)
    (tl : bridge_equiv (listBridge b) rs ms) :
    bridge_equiv (listBridge b) (r :: rs) (m :: ms) := by
  unfold bridge_equiv at *
  unfold listBridge at *
  simp [List.map] at *
  exact ⟨hd, tl⟩

-- List equivalence implies same length
theorem list_equiv_length (b : Bridge R M) [DecidableEq b.Observed]
    (rs : List R) (ms : List M)
    (h : bridge_equiv (listBridge b) rs ms) :
    rs.length = ms.length := by
  unfold bridge_equiv listBridge at h
  simp at h
  have := congrArg List.length h
  simp at this
  exact this

-- Product bridge equivalence is equivalent to component equivalence
theorem prod_equiv_iff (bA : Bridge RA MA) (bB : Bridge RB MB)
    [DecidableEq bA.Observed] [DecidableEq bB.Observed]
    (ra : RA) (ma : MA) (rb : RB) (mb : MB) :
    bridge_equiv (prodBridge bA bB) (ra, rb) (ma, mb)
    ↔ (bridge_equiv bA ra ma ∧ bridge_equiv bB rb mb) := by
  unfold bridge_equiv prodBridge
  simp [Prod.mk.injEq]

-- =========================================================================
-- Decidability
-- =========================================================================

/--
  Bridge equivalence is decidable. This connects the Lean `Prop`-level
  `bridge_equiv` to the Rust `check_bridge` computation, which returns
  `Result<(), String>`. The decidability comes from `DecidableEq` on
  the `Observed` type, which every bridge carries.
-/
instance bridge_equiv_decidable (b : Bridge R M) (r : R) (m : M) :
    Decidable (bridge_equiv b r m) := by
  unfold bridge_equiv
  exact b.dec_eq _ _

/--
  Bridge equivalence is either true or false -- it can be computed.
  This justifies the Rust `check_bridge` returning `Result<(), String>`:
  the check is a total function, not a partial one.
-/
theorem bridge_equiv_or_not (b : Bridge R M) (r : R) (m : M) :
    bridge_equiv b r m ∨ ¬ bridge_equiv b r m :=
  (bridge_equiv_decidable b r m).em

/--
  Bridge non-equivalence: observations differ.
-/
theorem bridge_not_equiv (b : Bridge R M) (r : R) (m : M) :
    ¬ bridge_equiv b r m ↔ b.observe_real r ≠ b.observe_model m := by
  unfold bridge_equiv
  exact Iff.rfl
