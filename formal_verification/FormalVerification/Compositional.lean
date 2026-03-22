/-
  Compositional Bisimulation

  Proves that bounded bisimulation composes: if two independent
  subsystems each satisfy bounded bisimulation, their product
  also satisfies bounded bisimulation.

  This enables modular testing: verify each subsystem independently,
  then conclude that their composition is correct — without testing
  the composed system directly.

  Independence means: actions from subsystem A don't affect the
  state of subsystem B, and vice versa. This is modeled by the
  product construction where each subsystem has its own state
  and step functions.

  Corresponds to `compositional.rs` in the Rust library.
-/

import FormalVerification.Lockstep

-- =========================================================================
-- Product system
-- =========================================================================

/--
  The product of two lockstep systems. Actions are from the disjoint
  union of both action spaces. Each action only affects its own
  subsystem's state — the other subsystem's state is unchanged.
-/
def product_system (sys1 sys2 : LockstepSystem) : LockstepSystem where
  SM := sys1.SM × sys2.SM
  SS := sys1.SS × sys2.SS
  ActionIdx := sys1.ActionIdx ⊕ sys2.ActionIdx
  RetM := fun
    | .inl a => sys1.RetM a
    | .inr a => sys2.RetM a
  RetS := fun
    | .inl a => sys1.RetS a
    | .inr a => sys2.RetS a
  bridge := fun
    | .inl a => sys1.bridge a
    | .inr a => sys2.bridge a
  step_model := fun
    | .inl a => fun (sm1, sm2) =>
        let (sm1', r) := sys1.step_model a sm1
        ((sm1', sm2), r)
    | .inr a => fun (sm1, sm2) =>
        let (sm2', r) := sys2.step_model a sm2
        ((sm1, sm2'), r)
  step_sut := fun
    | .inl a => fun (ss1, ss2) =>
        let (ss1', r) := sys1.step_sut a ss1
        ((ss1', ss2), r)
    | .inr a => fun (ss1, ss2) =>
        let (ss2', r) := sys2.step_sut a ss2
        ((ss1, ss2'), r)

-- =========================================================================
-- Compositional bisimulation theorem
-- =========================================================================

/--
  **Compositional bisimulation**: if both subsystems satisfy bounded
  bisimulation at depth n, their product also satisfies bounded
  bisimulation at depth n.

  This is the key modular testing theorem: test each subsystem
  independently, conclude the composition is correct.
-/
theorem compositional_bisim (sys1 sys2 : LockstepSystem)
    (n : Nat) (sm1 : sys1.SM) (ss1 : sys1.SS)
    (sm2 : sys2.SM) (ss2 : sys2.SS)
    (h1 : bounded_bisim sys1 n sm1 ss1)
    (h2 : bounded_bisim sys2 n sm2 ss2) :
    bounded_bisim (product_system sys1 sys2) n (sm1, sm2) (ss1, ss2) := by
  induction n generalizing sm1 ss1 sm2 ss2 with
  | zero => trivial
  | succ k ih =>
    simp only [bounded_bisim]
    intro a
    match a with
    | .inl a1 =>
      simp only [product_system]
      simp only [bounded_bisim] at h1
      have ha1 := h1 a1
      have h2k := bounded_bisim_mono sys2 k (k + 1) sm2 ss2 (by omega) h2
      exact ⟨ha1.1, ih _ _ _ _ ha1.2 h2k⟩
    | .inr a2 =>
      simp only [product_system]
      simp only [bounded_bisim] at h2
      have ha2 := h2 a2
      have h1k := bounded_bisim_mono sys1 k (k + 1) sm1 ss1 (by omega) h1
      exact ⟨ha2.1, ih _ _ _ _ h1k ha2.2⟩

/--
  **Converse: product bisim implies component bisim (left).**
  If the product satisfies bounded bisimulation, the left
  subsystem does too.
-/
theorem product_bisim_left (sys1 sys2 : LockstepSystem)
    (n : Nat) (sm1 : sys1.SM) (ss1 : sys1.SS)
    (sm2 : sys2.SM) (ss2 : sys2.SS)
    (h : bounded_bisim (product_system sys1 sys2) n (sm1, sm2) (ss1, ss2)) :
    bounded_bisim sys1 n sm1 ss1 := by
  induction n generalizing sm1 ss1 sm2 ss2 with
  | zero => trivial
  | succ k ih =>
    simp only [bounded_bisim] at h ⊢
    intro a1
    have hp := h (.inl a1)
    simp only [product_system] at hp
    exact ⟨hp.1, ih _ _ sm2 ss2 hp.2⟩

/--
  **Converse: product bisim implies component bisim (right).**
-/
theorem product_bisim_right (sys1 sys2 : LockstepSystem)
    (n : Nat) (sm1 : sys1.SM) (ss1 : sys1.SS)
    (sm2 : sys2.SM) (ss2 : sys2.SS)
    (h : bounded_bisim (product_system sys1 sys2) n (sm1, sm2) (ss1, ss2)) :
    bounded_bisim sys2 n sm2 ss2 := by
  induction n generalizing sm1 ss1 sm2 ss2 with
  | zero => trivial
  | succ k ih =>
    simp only [bounded_bisim] at h ⊢
    intro a2
    have hp := h (.inr a2)
    simp only [product_system] at hp
    exact ⟨hp.1, ih sm1 ss1 _ _ hp.2⟩

/--
  **Biconditional: product bisim iff both components.**
  The product satisfies bounded bisimulation at depth n iff
  and only if both components do.
-/
theorem product_bisim_iff (sys1 sys2 : LockstepSystem)
    (n : Nat) (sm1 : sys1.SM) (ss1 : sys1.SS)
    (sm2 : sys2.SM) (ss2 : sys2.SS) :
    bounded_bisim (product_system sys1 sys2) n (sm1, sm2) (ss1, ss2)
    ↔ bounded_bisim sys1 n sm1 ss1 ∧ bounded_bisim sys2 n sm2 ss2 := by
  constructor
  · intro h
    exact ⟨product_bisim_left sys1 sys2 n sm1 ss1 sm2 ss2 h,
           product_bisim_right sys1 sys2 n sm1 ss1 sm2 ss2 h⟩
  · intro ⟨h1, h2⟩
    exact compositional_bisim sys1 sys2 n sm1 ss1 sm2 ss2 h1 h2

-- =========================================================================
-- Monoidal structure: associativity and vacuous component
-- =========================================================================

/--
  **Vacuous component**: if a system has no actions (`ActionIdx` is
  empty), bounded bisimulation holds trivially at any depth.
-/
theorem empty_action_bisim (sys : LockstepSystem)
    (hempty : sys.ActionIdx → False)
    (n : Nat) (sm : sys.SM) (ss : sys.SS) :
    bounded_bisim sys n sm ss := by
  induction n generalizing sm ss with
  | zero => trivial
  | succ k ih =>
    simp only [bounded_bisim]
    intro a; exact (hempty a).elim

/--
  **Associativity**: product composition is associative up to
  bisimulation. `(sys1 ⊗ sys2) ⊗ sys3 ↔ sys1 ⊗ (sys2 ⊗ sys3)`
  at every depth.
-/
theorem product_assoc (sys1 sys2 sys3 : LockstepSystem)
    (n : Nat)
    (sm1 : sys1.SM) (ss1 : sys1.SS)
    (sm2 : sys2.SM) (ss2 : sys2.SS)
    (sm3 : sys3.SM) (ss3 : sys3.SS) :
    bounded_bisim (product_system (product_system sys1 sys2) sys3)
      n ((sm1, sm2), sm3) ((ss1, ss2), ss3)
    ↔ bounded_bisim (product_system sys1 (product_system sys2 sys3))
      n (sm1, (sm2, sm3)) (ss1, (ss2, ss3)) := by
  rw [product_bisim_iff, product_bisim_iff, product_bisim_iff, product_bisim_iff]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩,
         fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
