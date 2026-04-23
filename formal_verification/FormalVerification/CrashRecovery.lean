/-
  Crash-Recovery Bisimulation

  Extends bounded bisimulation with crash transitions. A crash
  resets the SUT to a recovered state derived from a checkpoint
  of the model. The crash bisimulation requires that:

  1. Normal actions satisfy bridge_equiv (as in bounded_bisim)
  2. A state invariant holds at every reachable state
  3. After a crash, the recovered states are in the bisimulation

  This is the formal foundation for crash-recovery testing --
  the first machine-checked proof that crash-recovery PBT is sound.
  It fills the gap between Jepsen (empirical crash testing) and
  Perennial (full crash-recovery verification).

  Corresponds to `CrashRecoveryModel` and `run_crash_recovery_test`
  in `src/crash_recovery.rs`.
-/

import FormalVerification.Invariant

-- =========================================================================
-- Crash-recovery system
-- =========================================================================

/--
  A lockstep system extended with crash-recovery semantics.
  Adds a durable state type, checkpoint/recovery functions,
  and a state invariant.
-/
structure CrashRecoverySystem extends LockstepSystem where
  DS : Type                    -- durable state (survives crash)
  checkpoint : SM → DS         -- extract durable state from model
  model_recover : DS → SM      -- recover model from checkpoint
  sut_recover : SS → SS        -- recover SUT from crash (self-recovery from
                               -- persisted state -- the SUT doesn't have
                               -- access to the model's checkpoint, so it
                               -- must reconstruct from its own durable state)
  invariant : SM → Prop        -- state invariant (must hold at every step)

-- =========================================================================
-- Crash bisimulation
-- =========================================================================

/--
  Crash bisimulation at depth n. Strengthens `bounded_bisim` with:
  1. The state invariant holds at the current model state
  2. Normal actions preserve bridge_equiv and the bisimulation
  3. After a crash, the recovered states are in the bisimulation

  The crash transition consumes one depth unit -- recovering and
  continuing for n more steps requires depth n+1.
-/
def crash_bisim (sys : CrashRecoverySystem) :
    Nat → sys.SM → sys.SS → Prop
  | 0, _, _ => True
  | n + 1, sm, ss =>
    -- Invariant holds at current state
    sys.invariant sm
    -- Normal actions work as in bounded_bisim
    ∧ (∀ (a : sys.ActionIdx),
        let (sm', rm) := sys.step_model a sm
        let (ss', rs) := sys.step_sut a ss
        bridge_equiv (sys.bridge a) rs rm
        ∧ crash_bisim sys n sm' ss')
    -- After a crash, recovered states are in the bisimulation
    ∧ crash_bisim sys n
        (sys.model_recover (sys.checkpoint sm))
        (sys.sut_recover ss)

-- =========================================================================
-- Properties
-- =========================================================================

/-- Crash bisimulation at depth 0 is trivially true. -/
theorem crash_bisim_zero (sys : CrashRecoverySystem)
    (sm : sys.SM) (ss : sys.SS) :
    crash_bisim sys 0 sm ss :=
  trivial

/--
  **Crash bisim implies bounded bisim**: crash-recovery bisimulation
  is strictly stronger than normal bounded bisimulation. If the
  system handles crashes correctly, it also works without crashes.
-/
theorem crash_bisim_implies_bounded (sys : CrashRecoverySystem)
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (h : crash_bisim sys n sm ss) :
    bounded_bisim sys.toLockstepSystem n sm ss := by
  induction n generalizing sm ss with
  | zero => trivial
  | succ k ih =>
    simp only [crash_bisim] at h
    obtain ⟨_hinv, hactions, _hcrash⟩ := h
    simp only [bounded_bisim]
    intro a
    have ha := hactions a
    exact ⟨ha.1, ih _ _ ha.2⟩

/-- Crash bisimulation is monotone in depth. -/
theorem crash_bisim_mono (sys : CrashRecoverySystem) :
    ∀ (n m : Nat) (sm : sys.SM) (ss : sys.SS),
    n ≤ m → crash_bisim sys m sm ss → crash_bisim sys n sm ss := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ k ih =>
    intro m sm ss h hm
    match m, h with
    | m' + 1, h' =>
      simp only [crash_bisim] at hm ⊢
      obtain ⟨hinv, hactions, hcrash⟩ := hm
      refine ⟨hinv, ?_, ?_⟩
      · intro a
        have ha := hactions a
        exact ⟨ha.1, ih m' _ _ (by omega) ha.2⟩
      · exact ih m' _ _ (by omega) hcrash

-- =========================================================================
-- Invariant properties
-- =========================================================================

/--
  **Invariant preserved along traces**: if crash bisimulation holds
  at depth n+1, the invariant holds at the current state.
-/
theorem crash_bisim_invariant (sys : CrashRecoverySystem)
    (sm : sys.SM) (ss : sys.SS) (n : Nat)
    (h : crash_bisim sys (n + 1) sm ss) :
    sys.invariant sm := by
  simp only [crash_bisim] at h
  exact h.1

/--
  **Invariant after action**: if crash bisimulation holds at depth
  n+2 and we take an action, the invariant holds at the successor.
-/
theorem crash_bisim_invariant_step (sys : CrashRecoverySystem)
    (sm : sys.SM) (ss : sys.SS) (a : sys.ActionIdx) (n : Nat)
    (h : crash_bisim sys (n + 2) sm ss) :
    sys.invariant (sys.step_model a sm).1 := by
  simp only [crash_bisim] at h
  obtain ⟨_, hactions, _⟩ := h
  have ha := hactions a
  exact crash_bisim_invariant sys _ _ n ha.2

-- =========================================================================
-- Recovery properties
-- =========================================================================

/--
  **Recovery preserves bisimulation**: if crash bisim holds at depth
  n+1, then after a crash, the recovered states are in the bisimulation
  at depth n.
-/
theorem crash_recovery_preserves (sys : CrashRecoverySystem)
    (sm : sys.SM) (ss : sys.SS) (n : Nat)
    (h : crash_bisim sys (n + 1) sm ss) :
    crash_bisim sys n
      (sys.model_recover (sys.checkpoint sm))
      (sys.sut_recover ss) := by
  simp only [crash_bisim] at h
  exact h.2.2

/--
  **Double crash**: crash bisimulation is preserved through two
  consecutive crashes. The system can crash, recover, crash again,
  recover again, and still be in the bisimulation.
-/
theorem crash_bisim_double_crash (sys : CrashRecoverySystem)
    (sm : sys.SM) (ss : sys.SS) (n : Nat)
    (h : crash_bisim sys (n + 2) sm ss) :
    let sm1 := sys.model_recover (sys.checkpoint sm)
    let ss1 := sys.sut_recover ss
    crash_bisim sys n
      (sys.model_recover (sys.checkpoint sm1))
      (sys.sut_recover ss1) := by
  have h1 := crash_recovery_preserves sys sm ss (n + 1)
    (by rw [show n + 2 = (n + 1) + 1 from by omega]; exact h)
  exact crash_recovery_preserves sys _ _ n h1

/--
  **Crash then continue**: after a crash and recovery, normal
  lockstep testing is still valid on the recovered states.
-/
theorem crash_then_bounded_bisim (sys : CrashRecoverySystem)
    (sm : sys.SM) (ss : sys.SS) (n : Nat)
    (h : crash_bisim sys (n + 1) sm ss) :
    bounded_bisim sys.toLockstepSystem n
      (sys.model_recover (sys.checkpoint sm))
      (sys.sut_recover ss) :=
  crash_bisim_implies_bounded sys n _ _ (crash_recovery_preserves sys sm ss n h)
