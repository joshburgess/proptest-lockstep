/-
  State Invariants

  Shared infrastructure for per-step state invariants. An invariant
  is a predicate on the model state that must hold at every reachable
  state. This module provides the core definitions and theorems used
  by crash-recovery, commutativity specs, eventual consistency, and
  other extensions.

  Corresponds to `InvariantModel` in `src/invariant.rs`.
-/

import FormalVerification.Lockstep

-- =========================================================================
-- Invariant system
-- =========================================================================

/--
  A lockstep system extended with a state invariant.
  The invariant must hold at every reachable model state.
-/
structure InvariantSystem extends LockstepSystem where
  invariant : SM → Prop

-- =========================================================================
-- Invariant-preserving bisimulation
-- =========================================================================

/--
  Bounded bisimulation with invariant checking.
  Like `bounded_bisim` but additionally requires the invariant to
  hold at every reachable model state.
-/
def invariant_bisim (sys : InvariantSystem) :
    Nat → sys.SM → sys.SS → Prop
  | 0, _, _ => True
  | n + 1, sm, ss =>
    sys.invariant sm
    ∧ ∀ (a : sys.ActionIdx),
        let (sm', rm) := sys.step_model a sm
        let (ss', rs) := sys.step_sut a ss
        bridge_equiv (sys.bridge a) rs rm
        ∧ invariant_bisim sys n sm' ss'

-- =========================================================================
-- Properties
-- =========================================================================

/-- Invariant bisim at depth 0 is trivially true. -/
theorem invariant_bisim_zero (sys : InvariantSystem)
    (sm : sys.SM) (ss : sys.SS) :
    invariant_bisim sys 0 sm ss :=
  trivial

/--
  **Invariant bisim implies bounded bisim**: invariant-checking
  bisimulation is strictly stronger than plain bounded bisimulation.
-/
theorem invariant_bisim_implies_bounded (sys : InvariantSystem)
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (h : invariant_bisim sys n sm ss) :
    bounded_bisim sys.toLockstepSystem n sm ss := by
  induction n generalizing sm ss with
  | zero => trivial
  | succ k ih =>
    simp only [invariant_bisim] at h
    obtain ⟨_, hactions⟩ := h
    simp only [bounded_bisim]
    intro a
    have ha := hactions a
    exact ⟨ha.1, ih _ _ ha.2⟩

/--
  **Invariant holds at current state**: if invariant bisim holds at
  depth n+1, the invariant holds at the current model state.
-/
theorem invariant_bisim_holds (sys : InvariantSystem)
    (sm : sys.SM) (ss : sys.SS) (n : Nat)
    (h : invariant_bisim sys (n + 1) sm ss) :
    sys.invariant sm := by
  simp only [invariant_bisim] at h
  exact h.1

/--
  **Invariant holds at successor**: if invariant bisim holds at depth
  n+2, the invariant holds at the successor state after any action.
-/
theorem invariant_bisim_holds_step (sys : InvariantSystem)
    (sm : sys.SM) (ss : sys.SS) (a : sys.ActionIdx) (n : Nat)
    (h : invariant_bisim sys (n + 2) sm ss) :
    sys.invariant (sys.step_model a sm).1 := by
  simp only [invariant_bisim] at h
  obtain ⟨_, hactions⟩ := h
  have ha := hactions a
  exact (invariant_bisim_holds sys _ _ n ha.2)

/-- Invariant bisimulation is monotone in depth. -/
theorem invariant_bisim_mono (sys : InvariantSystem) :
    ∀ (n m : Nat) (sm : sys.SM) (ss : sys.SS),
    n ≤ m → invariant_bisim sys m sm ss → invariant_bisim sys n sm ss := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ k ih =>
    intro m sm ss h hm
    match m, h with
    | m' + 1, h' =>
      simp only [invariant_bisim] at hm ⊢
      obtain ⟨hinv, hactions⟩ := hm
      refine ⟨hinv, ?_⟩
      intro a
      have ha := hactions a
      exact ⟨ha.1, ih m' _ _ (by omega) ha.2⟩

/--
  **Invariant along trace**: if invariant bisim holds at depth n,
  the invariant holds at every state reachable within n steps.
  This is the key theorem that extensions (crash-recovery, etc.)
  build on.
-/
theorem invariant_along_trace (sys : InvariantSystem)
    (trace : List sys.ActionIdx) (sm : sys.SM) (ss : sys.SS)
    (h : invariant_bisim sys (trace.length + 1) sm ss) :
    sys.invariant sm := by
  exact invariant_bisim_holds sys sm ss trace.length h
