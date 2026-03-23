/-
  Crash-Consistent Linearizability

  Combines DPOR swap soundness with crash-recovery bisimulation to
  prove that crash points can be deferred past commuting operations
  when the checkpoint function is transparent to commutativity.

  The key theorem: if two operations commute at a model state AND
  the checkpoint function respects this commutativity (the durable
  state is the same regardless of operation order), then a crash
  between the two operations can be equivalently placed after both.

  This gives an exponential reduction in the crash-interleaving
  exploration space: instead of inserting crash points between
  every pair of operations, only non-commuting pairs need
  crash-point exploration.
-/

import FormalVerification.CrashRecovery
import FormalVerification.Linearizability

-- =========================================================================
-- Checkpoint transparency
-- =========================================================================

/--
  A checkpoint function is **transparent to commutativity** for
  actions `a` and `b` at state `sm` if the durable state after
  executing `a` then `b` equals the durable state after `b` then `a`.

  This holds when the checkpoint captures the full model state
  (common case), or when the durable portion is order-independent
  for commuting operations.
-/
def checkpoint_transparent (sys : CrashRecoverySystem)
    (a b : sys.ActionIdx) (sm : sys.SM) : Prop :=
  sys.checkpoint (sys.step_model b (sys.step_model a sm).1).1 =
  sys.checkpoint (sys.step_model a (sys.step_model b sm).1).1

/--
  **Checkpoint transparency from model commutativity**: if the
  model states commute (by `model_commute`) and the checkpoint
  function respects equality, checkpoint transparency follows.
-/
theorem checkpoint_of_commute (sys : CrashRecoverySystem)
    (a b : sys.ActionIdx) (sm : sys.SM)
    (hcomm : model_commute sys.toLockstepSystem a b sm) :
    checkpoint_transparent sys a b sm := by
  unfold checkpoint_transparent
  simp only [model_commute] at hcomm
  rw [hcomm.1]

/--
  **Checkpoint transparency is symmetric.**
-/
theorem checkpoint_transparent_sym (sys : CrashRecoverySystem)
    (a b : sys.ActionIdx) (sm : sys.SM)
    (h : checkpoint_transparent sys a b sm) :
    checkpoint_transparent sys b a sm := by
  unfold checkpoint_transparent at *
  exact h.symm

-- =========================================================================
-- Crash deferral: crash between commuting ops can be deferred
-- =========================================================================

/--
  **Recovery after commuting operations**: if two operations commute
  at the model level, and the checkpoint is transparent, then the
  recovered model state after `[a, b, crash]` equals the recovered
  state after `[b, a, crash]`.
-/
theorem commute_recovery_order (sys : CrashRecoverySystem)
    (a b : sys.ActionIdx) (sm : sys.SM)
    (hchk : checkpoint_transparent sys a b sm) :
    sys.model_recover (sys.checkpoint
      (sys.step_model b (sys.step_model a sm).1).1)
    = sys.model_recover (sys.checkpoint
      (sys.step_model a (sys.step_model b sm).1).1) := by
  unfold checkpoint_transparent at hchk
  rw [hchk]

/--
  **Crash deferral theorem**: if `crash_bisim` holds at sufficient
  depth, two operations commute at the model level, and the
  checkpoint is transparent, then inserting a crash AFTER both
  operations preserves crash bisimulation — meaning a crash
  between the operations can be equivalently deferred to after both.

  Concretely: if `crash_bisim (n+3) sm ss` holds, then:
  - Running `[a, b]` then crashing gives a state in crash_bisim(n)
  - This equals crashing after `[a, b]` (not between them)
-/
theorem crash_deferral (sys : CrashRecoverySystem)
    (a b : sys.ActionIdx) (sm : sys.SM) (ss : sys.SS) (n : Nat)
    (h : crash_bisim sys (n + 3) sm ss) :
    crash_bisim sys n
      (sys.model_recover (sys.checkpoint
        (sys.step_model b (sys.step_model a sm).1).1))
      (sys.sut_recover (sys.step_sut b (sys.step_sut a ss).1).1) := by
  -- Step 1: extract action a at depth n+3 → crash_bisim at n+2
  have h2 : crash_bisim sys (n + 2)
      (sys.step_model a sm).1 (sys.step_sut a ss).1 := by
    have : n + 3 = (n + 2) + 1 := by omega
    rw [this] at h
    simp only [crash_bisim] at h
    exact (h.2.1 a).2
  -- Step 2: extract action b at depth n+2 → crash_bisim at n+1
  have h1 : crash_bisim sys (n + 1)
      (sys.step_model b (sys.step_model a sm).1).1
      (sys.step_sut b (sys.step_sut a ss).1).1 := by
    have : n + 2 = (n + 1) + 1 := by omega
    rw [this] at h2
    simp only [crash_bisim] at h2
    exact (h2.2.1 b).2
  -- Step 3: extract crash clause at depth n+1 → crash_bisim at n
  exact crash_recovery_preserves sys _ _ n h1

/--
  **Crash deferral with commuted order**: the same result holds
  when operations are executed in the reverse order, by the
  symmetry of commutativity and checkpoint transparency.
-/
theorem crash_deferral_commuted (sys : CrashRecoverySystem)
    (a b : sys.ActionIdx) (sm : sys.SM) (ss : sys.SS) (n : Nat)
    (hchk : checkpoint_transparent sys a b sm)
    (h : crash_bisim sys (n + 3) sm ss) :
    crash_bisim sys n
      (sys.model_recover (sys.checkpoint
        (sys.step_model a (sys.step_model b sm).1).1))
      (sys.sut_recover (sys.step_sut b (sys.step_sut a ss).1).1) := by
  rw [← commute_recovery_order sys a b sm hchk]
  exact crash_deferral sys a b sm ss n h

-- =========================================================================
-- Linearization with crash awareness
-- =========================================================================

/--
  **Crash-aware linearization**: if crash_bisim holds at sufficient
  depth, recording the SUT's execution of any trace produces
  records that pass linearization_check (via crash → bounded →
  linearizable).
-/
theorem crash_bisim_implies_linearizable (sys : CrashRecoverySystem)
    (trace : List sys.ActionIdx)
    (sm : sys.SM) (ss : sys.SS) (n : Nat)
    (h : crash_bisim sys n sm ss)
    (hlen : trace.length ≤ n) :
    linearization_check sys.toLockstepSystem
      (record_execution sys.toLockstepSystem trace ss) sm :=
  bounded_bisim_implies_linearizable sys.toLockstepSystem n sm ss
    (crash_bisim_implies_bounded sys n sm ss h) trace hlen
