/-
  Lockstep Bisimulation

  Defines the lockstep testing relation as a bounded bisimulation
  between a model and a system-under-test (SUT), parameterized by
  bridges that determine what is observed.
-/

import FormalVerification.Bridge

/--
  A lockstep system ties together model and SUT with actions and bridges.
-/
structure LockstepSystem where
  SM : Type          -- Model state
  SS : Type          -- SUT state
  ActionIdx : Type   -- Action index
  RetM : ActionIdx → Type  -- Model return type per action
  RetS : ActionIdx → Type  -- SUT return type per action
  bridge : (a : ActionIdx) → Bridge (RetS a) (RetM a)
  step_model : (a : ActionIdx) → SM → SM × RetM a
  step_sut : (a : ActionIdx) → SS → SS × RetS a

/--
  Bounded bisimulation at depth n.
  R_0 is trivially true; R_{n+1} requires one-step agreement
  and successor states in R_n.
-/
def bounded_bisim (sys : LockstepSystem) :
    Nat → sys.SM → sys.SS → Prop
  | 0, _, _ => True
  | n + 1, sm, ss =>
    ∀ (a : sys.ActionIdx),
      let (sm', rm) := sys.step_model a sm
      let (ss', rs) := sys.step_sut a ss
      bridge_equiv (sys.bridge a) rs rm
      ∧ bounded_bisim sys n sm' ss'

/-- Full (coinductive) bisimulation: bounded bisim at every depth. -/
def lockstep_bisim (sys : LockstepSystem) (sm : sys.SM) (ss : sys.SS) : Prop :=
  ∀ n, bounded_bisim sys n sm ss

-- =========================================================================
-- Properties
-- =========================================================================

theorem bounded_bisim_zero (sys : LockstepSystem) (sm : sys.SM) (ss : sys.SS) :
    bounded_bisim sys 0 sm ss :=
  trivial

theorem bounded_bisim_mono (sys : LockstepSystem) :
    ∀ (n m : Nat) (sm : sys.SM) (ss : sys.SS),
    n ≤ m → bounded_bisim sys m sm ss → bounded_bisim sys n sm ss := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ k ih =>
    intro m sm ss h hm
    match m, h with
    | m' + 1, h' =>
      simp only [bounded_bisim] at hm ⊢
      intro a
      obtain ⟨hequiv, hrest⟩ := hm a
      exact ⟨hequiv, ih m' _ _ (by omega) hrest⟩

theorem bisim_implies_bounded (sys : LockstepSystem) (sm : sys.SM) (ss : sys.SS)
    (h : lockstep_bisim sys sm ss) (n : Nat) :
    bounded_bisim sys n sm ss :=
  h n

theorem bounded_bisim_mono' (sys : LockstepSystem) (sm : sys.SM) (ss : sys.SS)
    (n m : Nat) (h : n ≤ m) (hm : bounded_bisim sys m sm ss) :
    bounded_bisim sys n sm ss :=
  bounded_bisim_mono sys n m sm ss h hm

/-- Single-step agreement implies bounded bisim at depth 1. -/
theorem single_step_bisim (sys : LockstepSystem) (sm : sys.SM) (ss : sys.SS)
    (h : ∀ a, bridge_equiv (sys.bridge a) (sys.step_sut a ss).2 (sys.step_model a sm).2) :
    bounded_bisim sys 1 sm ss := by
  simp only [bounded_bisim]
  intro a
  constructor
  · exact h a
  · trivial
