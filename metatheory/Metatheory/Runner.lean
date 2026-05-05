/-
  Runner Correspondence

  Models the test runner's operational behavior as a trace-based
  predicate and proves it corresponds exactly to bounded bisimulation.

  The Rust runner (LockstepSut::apply) processes a sequence of actions:
  for each action, it runs the model and SUT, checks bridge equivalence,
  and continues. This file formalizes that process and proves:

    runner passes on all traces of length n  ↔  bounded_bisim n
-/

import Metatheory.Lockstep

/--
  The runner checks a specific trace (list of actions).
  Mirrors `LockstepSut::apply` in the Rust implementation:
  1. Run step_model → (sm', rm)
  2. Run step_sut → (ss', rs)
  3. Check bridge_equiv on results
  4. Continue with successor states
-/
def runner_passes (sys : LockstepSystem) :
    List sys.ActionIdx → sys.SM → sys.SS → Prop
  | [], _, _ => True
  | a :: rest, sm, ss =>
    let (sm', rm) := sys.step_model a sm
    let (ss', rs) := sys.step_sut a ss
    bridge_equiv (sys.bridge a) rs rm
    ∧ runner_passes sys rest sm' ss'

/-- Empty trace always passes. -/
theorem runner_passes_nil (sys : LockstepSystem) (sm : sys.SM) (ss : sys.SS) :
    runner_passes sys [] sm ss :=
  trivial

/-- Single-step runner: bridge check on one action. -/
theorem runner_passes_single (sys : LockstepSystem) (sm : sys.SM) (ss : sys.SS)
    (a : sys.ActionIdx)
    (h : bridge_equiv (sys.bridge a) (sys.step_sut a ss).2 (sys.step_model a sm).2) :
    runner_passes sys [a] sm ss := by
  simp only [runner_passes]
  exact ⟨h, trivial⟩

-- =========================================================================
-- The Main Correspondence
-- =========================================================================

/--
  **Forward direction**: if the runner passes on ALL traces of length n,
  then bounded bisimulation holds at depth n.

  This is the key theorem that closes the formalization gap: the runner's
  operational checks (bridge_equiv at each step) establish the declarative
  bisimulation relation.
-/
theorem runner_implies_bounded_bisim (sys : LockstepSystem)
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (h : ∀ (trace : List sys.ActionIdx), trace.length = n →
         runner_passes sys trace sm ss) :
    bounded_bisim sys n sm ss := by
  induction n generalizing sm ss with
  | zero => trivial
  | succ k ih =>
    simp only [bounded_bisim]
    intro a
    -- Extract bridge_equiv from any trace starting with a
    have hcons : ∀ (rest : List sys.ActionIdx), rest.length = k →
        runner_passes sys (a :: rest) sm ss := by
      intro rest hlen
      exact h (a :: rest) (by simp [hlen])
    -- Get bridge check and tail from a specific trace
    have hany : runner_passes sys (a :: List.replicate k (a)) sm ss := by
      exact hcons (List.replicate k a) (by simp)
    simp only [runner_passes] at hany
    obtain ⟨hbridge, _⟩ := hany
    constructor
    · exact hbridge
    · -- Apply IH: need runner_passes on all traces of length k from successor states
      apply ih
      intro rest hlen
      have := hcons rest hlen
      simp only [runner_passes] at this
      exact this.2

/--
  **Reverse direction**: if bounded bisimulation holds at depth n,
  then the runner passes on any trace of length ≤ n.
-/
theorem bounded_bisim_implies_runner (sys : LockstepSystem)
    (trace : List sys.ActionIdx) (sm : sys.SM) (ss : sys.SS)
    (h : bounded_bisim sys trace.length sm ss) :
    runner_passes sys trace sm ss := by
  induction trace generalizing sm ss with
  | nil => trivial
  | cons a rest ih =>
    simp only [runner_passes]
    simp only [List.length, bounded_bisim] at h
    have ha := h a
    constructor
    · exact ha.1
    · exact ih _ _ ha.2

/--
  **The Runner Correspondence Theorem.**

  Passing on all traces of length n is equivalent to bounded
  bisimulation at depth n. This replaces the tautological
  `lockstep_test_sound` with a substantive connection between
  the runner's operational behavior and the bisimulation relation.
-/
theorem runner_bounded_bisim_equiv (sys : LockstepSystem)
    (n : Nat) (sm : sys.SM) (ss : sys.SS) :
    (∀ (trace : List sys.ActionIdx), trace.length = n →
     runner_passes sys trace sm ss)
    ↔ bounded_bisim sys n sm ss := by
  constructor
  · exact runner_implies_bounded_bisim sys n sm ss
  · intro h trace hlen
    have : bounded_bisim sys trace.length sm ss := by
      rw [hlen]; exact h
    exact bounded_bisim_implies_runner sys trace sm ss this
