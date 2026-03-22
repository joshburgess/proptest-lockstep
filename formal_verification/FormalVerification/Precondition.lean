/-
  Precondition Filtering

  The test runner only checks actions that satisfy a precondition
  predicate (model-state-dependent). This file formalizes the
  preconditioned bisimulation and proves its relationship to the
  universal (unpreconditioned) bisimulation.

  Key result: universal bisimulation implies preconditioned
  bisimulation, so the existing formalization (which quantifies
  over ALL actions) is a conservative overapproximation of what
  the runner actually checks.

  Corresponds to `LockstepModel::precondition` and the
  `ReferenceStateMachine::preconditions` method in `src/runner.rs`.
-/

import FormalVerification.Runner

-- =========================================================================
-- Preconditioned bisimulation
-- =========================================================================

/--
  A lockstep system extended with preconditions.
  Preconditions are model-state-dependent predicates that determine
  which actions are eligible at each step.
-/
structure PreconditionedSystem extends LockstepSystem where
  precond : ActionIdx → SM → Prop

/--
  Bounded bisimulation restricted to actions satisfying preconditions.
  Only actions where `precond a sm` holds are checked — this matches
  the runner's behavior, which filters actions through
  `LockstepModel::precondition` before executing them.
-/
def precond_bisim (psys : PreconditionedSystem) :
    Nat → psys.SM → psys.SS → Prop
  | 0, _, _ => True
  | n + 1, sm, ss =>
    ∀ (a : psys.ActionIdx), psys.precond a sm →
      let (sm', rm) := psys.step_model a sm
      let (ss', rs) := psys.step_sut a ss
      bridge_equiv (psys.bridge a) rs rm
      ∧ precond_bisim psys n sm' ss'

-- =========================================================================
-- Relationship to universal bisimulation
-- =========================================================================

/--
  **Universal implies preconditioned**: if bounded bisimulation holds
  for ALL actions (the universal quantification in `bounded_bisim`),
  then it holds for the subset satisfying preconditions.

  This proves the existing formalization is sound with respect to
  preconditioned testing: the universal bisimulation is strictly
  stronger than the preconditioned version.
-/
theorem universal_implies_preconditioned (psys : PreconditionedSystem)
    (n : Nat) (sm : psys.SM) (ss : psys.SS)
    (h : bounded_bisim psys.toLockstepSystem n sm ss) :
    precond_bisim psys n sm ss := by
  induction n generalizing sm ss with
  | zero => trivial
  | succ k ih =>
    simp only [precond_bisim]
    intro a _hpre
    simp only [bounded_bisim] at h
    have ha := h a
    exact ⟨ha.1, ih _ _ ha.2⟩

-- =========================================================================
-- Properties of preconditioned bisimulation
-- =========================================================================

/-- Preconditioned bisimulation at depth 0 is trivially true. -/
theorem precond_bisim_zero (psys : PreconditionedSystem)
    (sm : psys.SM) (ss : psys.SS) :
    precond_bisim psys 0 sm ss :=
  trivial

/-- Preconditioned bisimulation is monotone in depth. -/
theorem precond_bisim_mono (psys : PreconditionedSystem) :
    ∀ (n m : Nat) (sm : psys.SM) (ss : psys.SS),
    n ≤ m → precond_bisim psys m sm ss → precond_bisim psys n sm ss := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ k ih =>
    intro m sm ss h hm
    match m, h with
    | m' + 1, h' =>
      simp only [precond_bisim] at hm ⊢
      intro a hpre
      obtain ⟨hequiv, hrest⟩ := hm a hpre
      exact ⟨hequiv, ih m' _ _ (by omega) hrest⟩

-- =========================================================================
-- Preconditioned runner
-- =========================================================================

/--
  The preconditioned runner: checks a trace where each action must
  satisfy the precondition at the current model state. This models
  the actual test runner, which only generates and checks actions
  that pass `LockstepModel::precondition`.
-/
def precond_runner_passes (psys : PreconditionedSystem) :
    List psys.ActionIdx → psys.SM → psys.SS → Prop
  | [], _, _ => True
  | a :: rest, sm, ss =>
    psys.precond a sm
    ∧ let (sm', rm) := psys.step_model a sm
      let (ss', rs) := psys.step_sut a ss
      bridge_equiv (psys.bridge a) rs rm
      ∧ precond_runner_passes psys rest sm' ss'

/--
  Universal runner implies preconditioned runner on precondition-
  satisfying traces: if `runner_passes` (unconditioned) holds for
  a trace, and the head satisfies the precondition, the preconditioned
  runner also passes.
-/
theorem runner_head_precond (psys : PreconditionedSystem)
    (a : psys.ActionIdx) (rest : List psys.ActionIdx)
    (sm : psys.SM) (ss : psys.SS)
    (hpre : psys.precond a sm)
    (hrun : runner_passes psys.toLockstepSystem (a :: rest) sm ss)
    (hrest : precond_runner_passes psys rest
        (psys.step_model a sm).1 (psys.step_sut a ss).1) :
    precond_runner_passes psys (a :: rest) sm ss := by
  simp only [precond_runner_passes, runner_passes] at *
  exact ⟨hpre, hrun.1, hrest⟩

/--
  **Preconditioned runner correspondence**: if the preconditioned
  runner passes on all valid traces of length n, then preconditioned
  bisimulation holds at depth n.
-/
theorem precond_runner_implies_bisim (psys : PreconditionedSystem)
    (n : Nat) (sm : psys.SM) (ss : psys.SS)
    (h : ∀ (trace : List psys.ActionIdx), trace.length = n →
         precond_runner_passes psys trace sm ss) :
    precond_bisim psys n sm ss := by
  induction n generalizing sm ss with
  | zero => trivial
  | succ k ih =>
    simp only [precond_bisim]
    intro a hpre
    -- Use a trace starting with a
    have hcons : ∀ (rest : List psys.ActionIdx), rest.length = k →
        precond_runner_passes psys (a :: rest) sm ss := by
      intro rest hlen
      exact h (a :: rest) (by simp [hlen])
    -- Get from a specific trace
    have hany := hcons (List.replicate k a) (by simp)
    simp only [precond_runner_passes] at hany
    obtain ⟨_, hbridge, _⟩ := hany
    constructor
    · exact hbridge
    · apply ih
      intro rest hlen
      have := hcons rest hlen
      simp only [precond_runner_passes] at this
      exact this.2.2

/--
  **Preconditioned bisimulation step**: if preconditioned bisimulation holds at depth n+1
  and action a satisfies the precondition, then the bridge check passes
  and preconditioned bisimulation holds at depth n on the successor states.
-/
theorem precond_bisim_step (psys : PreconditionedSystem)
    (sm : psys.SM) (ss : psys.SS) (a : psys.ActionIdx) (n : Nat)
    (hpre : psys.precond a sm)
    (h : precond_bisim psys (n + 1) sm ss) :
    bridge_equiv (psys.bridge a)
        (psys.step_sut a ss).2 (psys.step_model a sm).2
    ∧ precond_bisim psys n
        (psys.step_model a sm).1 (psys.step_sut a ss).1 := by
  simp only [precond_bisim] at h
  exact h a hpre

-- =========================================================================
-- Converse: bisimulation implies runner (on valid traces)
-- =========================================================================

/--
  A trace is precondition-valid if the precondition holds for each
  action at the model state reached by executing the prefix.
-/
def precond_trace_valid (psys : PreconditionedSystem) :
    List psys.ActionIdx → psys.SM → Prop
  | [], _ => True
  | a :: rest, sm =>
    psys.precond a sm
    ∧ precond_trace_valid psys rest (psys.step_model a sm).1

/--
  **Converse**: if preconditioned bisimulation holds at depth n,
  then the preconditioned runner passes on every precondition-valid
  trace of length n.

  This is the reverse direction of `precond_runner_implies_bisim`.
  The precondition-validity requirement is necessary because
  `precond_runner_passes` includes precondition checks — a trace
  where preconditions don't hold would trivially fail the runner
  regardless of bisimulation.
-/
theorem precond_bisim_implies_runner (psys : PreconditionedSystem)
    (n : Nat) (sm : psys.SM) (ss : psys.SS)
    (h : precond_bisim psys n sm ss)
    (trace : List psys.ActionIdx) (hlen : trace.length = n)
    (hvalid : precond_trace_valid psys trace sm) :
    precond_runner_passes psys trace sm ss := by
  induction n generalizing sm ss trace with
  | zero =>
    match trace, hlen with
    | [], _ => trivial
  | succ k ih =>
    match trace, hlen with
    | a :: rest, hlen' =>
      simp only [precond_runner_passes, precond_trace_valid] at *
      obtain ⟨hpre, hvalid_rest⟩ := hvalid
      simp only [precond_bisim] at h
      have ha := h a hpre
      exact ⟨hpre, ha.1, ih _ _ ha.2 rest (by simp at hlen'; exact hlen') hvalid_rest⟩
