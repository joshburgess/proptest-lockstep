/-
  Projection Chains (GVar/Op Formalization)

  Formalizes the `Op` DSL -- the projection language for decomposing
  compound return types. Each projection is a partial function from
  a source type to a target type. Projections compose via Kleisli
  composition (the `Option` monad).

  The key result: projections PRESERVE bridge equivalence when the
  bridge structure matches the projection structure. If the source
  values are bridge-equivalent and the projection succeeds on both,
  the projected values are bridge-equivalent under the component bridge.

  This closes the GVar gap: the formal model now covers typed
  projection chains, matching the Rust `GVar<X, Y, O>` type.

  Corresponds to `Op<A, B>` in `src/op.rs` and `GVar` in `src/gvar.rs`.
-/

import FormalVerification.Bridge

-- =========================================================================
-- Projection type
-- =========================================================================

/--
  A projection from type A to type B. Projections are partial
  functions -- they return `Option B` because some projections
  can fail (e.g., extracting `Ok` from an `Err` value).

  This mirrors the Rust `Op<A, B>` trait.
-/
def Projection (A B : Type) := A → Option B

-- =========================================================================
-- Primitive projections
-- =========================================================================

/-- Identity projection: always succeeds. -/
def proj_id : Projection A A := fun a => some a

/-- First element of a product. -/
def proj_fst : Projection (A × B) A := fun (a, _) => some a

/-- Second element of a product. -/
def proj_snd : Projection (A × B) B := fun (_, b) => some b

/-- Ok projection on a sum (Result). Returns `none` on `inr`. -/
def proj_ok : Projection (A ⊕ B) A := fun
  | .inl a => some a
  | .inr _ => none

/-- Err projection on a sum (Result). Returns `none` on `inl`. -/
def proj_err : Projection (A ⊕ B) B := fun
  | .inl _ => none
  | .inr b => some b

/-- Some projection on Option. Returns `none` on `none`. -/
def proj_some : Projection (Option A) A := fun
  | some a => some a
  | none => none

/-- Index projection on List. Returns `none` if out of bounds. -/
def proj_index (i : Nat) : Projection (List A) A := fun xs =>
  xs[i]?

-- =========================================================================
-- Projection composition (Kleisli)
-- =========================================================================

/--
  Compose two projections. This is Kleisli composition for `Option`:
  first apply `f`, then apply `g` to the result. If either fails
  (returns `none`), the composition fails.

  Mirrors `OpComp<F, G, B>` in Rust.
-/
def proj_comp (f : Projection A B) (g : Projection B C) : Projection A C :=
  fun a => match f a with
    | some b => g b
    | none => none

-- =========================================================================
-- Projection properties
-- =========================================================================

/-- Identity is a left unit of composition. -/
theorem proj_comp_id_left (f : Projection A B) (a : A) :
    proj_comp proj_id f a = f a := by
  simp [proj_comp, proj_id]

/-- Identity is a right unit of composition. -/
theorem proj_comp_id_right (f : Projection A B) (a : A) :
    proj_comp f proj_id a = f a := by
  simp [proj_comp, proj_id]
  cases f a <;> simp

/-- Composition is associative. -/
theorem proj_comp_assoc (f : Projection A B) (g : Projection B C)
    (h : Projection C D) (a : A) :
    proj_comp (proj_comp f g) h a = proj_comp f (proj_comp g h) a := by
  simp [proj_comp]
  cases f a <;> simp

/-- Total projections always succeed. -/
theorem proj_fst_total (a : A) (b : B) :
    proj_fst (a, b) = some a := rfl

theorem proj_snd_total (a : A) (b : B) :
    proj_snd (a, b) = some b := rfl

theorem proj_id_total (a : A) :
    proj_id a = some a := rfl

/-- Partial projections succeed on the matching variant. -/
theorem proj_ok_inl (a : A) :
    @proj_ok A B (.inl a) = some a := rfl

theorem proj_ok_inr (b : B) :
    @proj_ok A B (.inr b) = none := rfl

theorem proj_err_inl (a : A) :
    @proj_err A B (.inl a) = none := rfl

theorem proj_err_inr (b : B) :
    @proj_err A B (.inr b) = some b := rfl

-- =========================================================================
-- Projections preserve bridge equivalence
-- =========================================================================

/--
  **Product projection preserves bridge_equiv (fst).**
  If `(ra, rb)` and `(ma, mb)` are product-bridge-equivalent,
  then `ra` and `ma` are component-bridge-equivalent.
-/
theorem proj_fst_preserves
    (bA : Bridge RA MA) (bB : Bridge RB MB)
    [DecidableEq bA.Observed] [DecidableEq bB.Observed]
    (ra : RA) (ma : MA) (rb : RB) (mb : MB)
    (h : bridge_equiv (prodBridge bA bB) (ra, rb) (ma, mb)) :
    bridge_equiv bA ra ma := by
  rw [prod_equiv_iff] at h
  exact h.1

/--
  **Product projection preserves bridge_equiv (snd).**
-/
theorem proj_snd_preserves
    (bA : Bridge RA MA) (bB : Bridge RB MB)
    [DecidableEq bA.Observed] [DecidableEq bB.Observed]
    (ra : RA) (ma : MA) (rb : RB) (mb : MB)
    (h : bridge_equiv (prodBridge bA bB) (ra, rb) (ma, mb)) :
    bridge_equiv bB rb mb := by
  rw [prod_equiv_iff] at h
  exact h.2

/--
  **Sum projection preserves bridge_equiv (ok).**
  If `inl(r)` and `inl(m)` are sum-bridge-equivalent, then
  `r` and `m` are ok-bridge-equivalent.
-/
theorem proj_ok_preserves
    (bOk : Bridge ROk MOk) (bErr : Bridge RErr MErr)
    [DecidableEq bOk.Observed] [DecidableEq bErr.Observed]
    (r : ROk) (m : MOk)
    (h : bridge_equiv (sumBridge bOk bErr) (.inl r) (.inl m)) :
    bridge_equiv bOk r m := by
  unfold bridge_equiv sumBridge at h
  simp at h
  exact h

/--
  **Sum projection preserves bridge_equiv (err).**
-/
theorem proj_err_preserves
    (bOk : Bridge ROk MOk) (bErr : Bridge RErr MErr)
    [DecidableEq bOk.Observed] [DecidableEq bErr.Observed]
    (r : RErr) (m : MErr)
    (h : bridge_equiv (sumBridge bOk bErr) (.inr r) (.inr m)) :
    bridge_equiv bErr r m := by
  unfold bridge_equiv sumBridge at h
  simp at h
  exact h

/--
  **Option projection preserves bridge_equiv.**
  If `some(r)` and `some(m)` are option-bridge-equivalent,
  then `r` and `m` are inner-bridge-equivalent.
-/
theorem proj_some_preserves
    (b : Bridge R M) [DecidableEq b.Observed]
    (r : R) (m : M)
    (h : bridge_equiv (optionBridge b) (some r) (some m)) :
    bridge_equiv b r m := by
  unfold bridge_equiv optionBridge at h
  simp at h
  exact h

-- =========================================================================
-- Composed projection preserves bridge_equiv
-- =========================================================================

/--
  **The fundamental GVar theorem**: a composed projection chain
  preserves bridge_equiv. If the source values are bridge-equivalent
  and both projections succeed, the projected values are bridge-
  equivalent under the target bridge.

  This is the theorem that justifies GVar: extracting a handle
  from `Result<(Handle, Path), Err>` via `OpOk.then(OpFst)` preserves
  bridge equivalence between the real handle and the model handle.

  Stated abstractly: for any projection that preserves bridge_equiv,
  the composition of two preserving projections also preserves it.
-/
theorem proj_comp_preserves
    {A B C : Type} {MA MB MC : Type}
    (bA : Bridge A MA) (bB : Bridge B MB) (bC : Bridge C MC)
    [DecidableEq bA.Observed] [DecidableEq bB.Observed] [DecidableEq bC.Observed]
    (f_real : Projection A B) (f_model : Projection MA MB)
    (g_real : Projection B C) (g_model : Projection MB MC)
    (a : A) (ma : MA)
    -- f preserves bridge_equiv
    (hf : ∀ a' ma', bridge_equiv bA a' ma' →
        ∀ b mb, f_real a' = some b → f_model ma' = some mb →
        bridge_equiv bB b mb)
    -- g preserves bridge_equiv
    (hg : ∀ b' mb', bridge_equiv bB b' mb' →
        ∀ c mc, g_real b' = some c → g_model mb' = some mc →
        bridge_equiv bC c mc)
    -- source values are bridge-equivalent
    (hab : bridge_equiv bA a ma)
    -- the composed projection succeeds on both sides
    (b : B) (mb : MB) (c : C) (mc : MC)
    (hfr : f_real a = some b) (hfm : f_model ma = some mb)
    (hgr : g_real b = some c) (hgm : g_model mb = some mc) :
    bridge_equiv bC c mc :=
  hg b mb (hf a ma hab b mb hfr hfm) c mc hgr hgm
