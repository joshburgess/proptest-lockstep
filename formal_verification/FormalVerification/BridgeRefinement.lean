/-
  Bridge Refinement Ordering

  Bridges form a preorder: bridge B1 refines bridge B2 if B1's
  equivalence relation is contained in B2's. This captures the
  precision of observation:

  - Transparent is the finest bridge (for types with the same
    observation functions): it requires equality of observations.
  - Opaque is the coarsest bridge: it relates everything.

  The lifts (sum, product, option, list) are monotone — they
  preserve the refinement ordering. This means that replacing a
  component bridge with a finer one produces a finer composite
  bridge, which gives strictly stronger guarantees.

  This formalization supports the "bridges as logical relations"
  pearl framing: the refinement ordering is a lattice structure
  on logical relations, with transparent at the top (identity
  relation) and opaque at the bottom (trivial relation).
-/

import FormalVerification.Lockstep

-- =========================================================================
-- Refinement ordering
-- =========================================================================

/--
  Bridge refinement: `b1` refines `b2` if every pair related by `b1`
  is also related by `b2`. A finer bridge gives a stronger guarantee.
-/
def bridge_refines (b1 b2 : Bridge R M) : Prop :=
  ∀ (r : R) (m : M), bridge_equiv b1 r m → bridge_equiv b2 r m

/-- Refinement is reflexive. -/
theorem refines_refl (b : Bridge R M) : bridge_refines b b :=
  fun _ _ h => h

/-- Refinement is transitive. -/
theorem refines_trans (b1 b2 b3 : Bridge R M)
    (h12 : bridge_refines b1 b2) (h23 : bridge_refines b2 b3) :
    bridge_refines b1 b3 :=
  fun r m h => h23 r m (h12 r m h)

-- =========================================================================
-- Opaque is the coarsest bridge
-- =========================================================================

/--
  **Opaque is coarsest**: every bridge refines the opaque bridge.
  Since opaque bridge_equiv is trivially true, any relation is
  contained in it.
-/
theorem opaque_coarsest (b : Bridge R M) :
    bridge_refines b (opaqueBridge R M) :=
  fun r m _ => opaqueBridge_always R M r m

/--
  Opaque is the unique coarsest bridge (up to equivalence):
  if a bridge relates all pairs, it is equivalent to opaque
  in the refinement ordering.
-/
theorem opaque_unique_coarsest (b : Bridge R M)
    (h : ∀ r m, bridge_equiv b r m) :
    bridge_refines (opaqueBridge R M) b :=
  fun r m _ => h r m

-- =========================================================================
-- Transparent: finest for identity-observed bridges
-- =========================================================================

/--
  **Transparent is finest among identity-observed bridges**: if a
  bridge over the same type uses the same observation function on
  both sides, then transparent refines it.

  This captures the intuition that equality (transparent) is the
  strongest possible equivalence when both sides are observed the
  same way.
-/
theorem transparent_refines_uniform (T : Type) [DecidableEq T]
    (b : Bridge T T)
    (huniform : ∀ x : T, b.observe_real x = b.observe_model x) :
    bridge_refines (transparent T) b := by
  intro r m h
  unfold bridge_equiv transparent at h
  simp [id] at h
  unfold bridge_equiv
  rw [h, huniform]

/--
  Transparent self-refinement: transparent refines itself.
  (Special case of reflexivity, stated for clarity.)
-/
theorem transparent_refines_self (T : Type) [DecidableEq T] :
    bridge_refines (transparent T) (transparent T) :=
  refines_refl _

-- =========================================================================
-- Lifts preserve refinement (monotonicity)
-- =========================================================================

/--
  **Sum lift is monotone**: if component bridges refine, the sum
  lift refines.
-/
theorem sum_refines
    (bOk1 bOk2 : Bridge ROk MOk) (bErr1 bErr2 : Bridge RErr MErr)
    [DecidableEq bOk1.Observed] [DecidableEq bErr1.Observed]
    [DecidableEq bOk2.Observed] [DecidableEq bErr2.Observed]
    (hOk : bridge_refines bOk1 bOk2)
    (hErr : bridge_refines bErr1 bErr2)
    -- Need a way to relate the lifted bridges
    -- Since they have different Observed types, we state it differently:
    -- Sum with finer components detects at least as many mismatches
    (r : ROk ⊕ RErr) (m : MOk ⊕ MErr)
    (h : bridge_equiv (sumBridge bOk1 bErr1) r m) :
    -- We can conclude the components are variant-matching and related
    match r, m with
    | .inl rok, .inl mok => bridge_equiv bOk2 rok mok
    | .inr rerr, .inr merr => bridge_equiv bErr2 rerr merr
    | .inl _, .inr _ => False
    | .inr _, .inl _ => False := by
  match r, m with
  | .inl rok, .inl mok =>
    unfold bridge_equiv sumBridge at h
    simp at h
    exact hOk rok mok h
  | .inr rerr, .inr merr =>
    unfold bridge_equiv sumBridge at h
    simp at h
    exact hErr rerr merr h
  | .inl _, .inr _ =>
    exact absurd h (sum_variant_mismatch_lr bOk1 bErr1 _ _)
  | .inr _, .inl _ =>
    exact absurd h (sum_variant_mismatch_rl bOk1 bErr1 _ _)

/--
  **Product lift is monotone**: if component bridges refine, the
  product lift refines.
-/
theorem prod_refines
    (bA1 bA2 : Bridge RA MA) (bB1 bB2 : Bridge RB MB)
    [DecidableEq bA1.Observed] [DecidableEq bB1.Observed]
    [DecidableEq bA2.Observed] [DecidableEq bB2.Observed]
    (hA : bridge_refines bA1 bA2) (hB : bridge_refines bB1 bB2)
    (ra : RA) (ma : MA) (rb : RB) (mb : MB)
    (h : bridge_equiv (prodBridge bA1 bB1) (ra, rb) (ma, mb)) :
    bridge_equiv bA2 ra ma ∧ bridge_equiv bB2 rb mb := by
  rw [prod_equiv_iff] at h
  exact ⟨hA ra ma h.1, hB rb mb h.2⟩

/--
  **Option lift is monotone**: if the inner bridge refines, the
  option lift refines.
-/
theorem option_refines
    (b1 b2 : Bridge R M)
    [DecidableEq b1.Observed] [DecidableEq b2.Observed]
    (h : bridge_refines b1 b2)
    (r : Option R) (m : Option M)
    (hequiv : bridge_equiv (optionBridge b1) r m) :
    match r, m with
    | some r', some m' => bridge_equiv b2 r' m'
    | none, none => True
    | _, _ => False := by
  match r, m with
  | some r', some m' =>
    unfold bridge_equiv optionBridge at hequiv
    simp at hequiv
    exact h r' m' hequiv
  | none, none => trivial
  | some _, none =>
    unfold bridge_equiv optionBridge at hequiv
    simp at hequiv
  | none, some _ =>
    unfold bridge_equiv optionBridge at hequiv
    simp at hequiv

/--
  **List lift is monotone**: if the inner bridge refines, then
  list bridge equivalence under b1 implies element-wise equivalence
  under b2.
-/
theorem list_refines
    (b1 b2 : Bridge R M)
    [DecidableEq b1.Observed] [DecidableEq b2.Observed]
    (href : bridge_refines b1 b2) :
    ∀ (rs : List R) (ms : List M),
    bridge_equiv (listBridge b1) rs ms →
    bridge_equiv (listBridge b2) rs ms := by
  intro rs
  induction rs with
  | nil =>
    intro ms hequiv
    unfold bridge_equiv listBridge at hequiv ⊢
    simp at hequiv ⊢
    match ms with
    | [] => rfl
    | _ :: _ => simp at hequiv
  | cons r rest ih =>
    intro ms hequiv
    match ms with
    | [] =>
      unfold bridge_equiv listBridge at hequiv
      simp at hequiv
    | m :: ms' =>
      unfold bridge_equiv listBridge at hequiv ⊢
      simp [List.map] at hequiv ⊢
      exact ⟨href r m hequiv.1, ih ms' hequiv.2⟩

-- =========================================================================
-- Refinement and bisimulation
-- =========================================================================

/--
  **Finer bridges give stronger bisimulation**: if system `sys1` has
  bridges that refine the corresponding bridges in `sys2` (with the
  same step functions), then bounded bisimulation under `sys1` implies
  bounded bisimulation under `sys2`.

  This means replacing opaque bridges with transparent ones (refining
  the observation) gives a strictly stronger guarantee.
-/
theorem refines_strengthen_bisim (sys : LockstepSystem)
    (bridge2 : (a : sys.ActionIdx) → Bridge (sys.RetS a) (sys.RetM a))
    (hrefine : ∀ a, bridge_refines (sys.bridge a) (bridge2 a))
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (h : bounded_bisim sys n sm ss) :
    bounded_bisim
      { sys with bridge := bridge2 }
      n sm ss := by
  induction n generalizing sm ss with
  | zero => trivial
  | succ k ih =>
    simp only [bounded_bisim] at h ⊢
    intro a
    have ha := h a
    exact ⟨hrefine a _ _ ha.1, ih _ _ ha.2⟩
