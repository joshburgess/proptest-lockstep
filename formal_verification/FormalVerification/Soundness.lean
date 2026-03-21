/-
  Soundness of Lockstep Testing

  The main theorems connecting lockstep testing to formal guarantees.
  The central result is `lockstep_test_sound`: if the runner passes
  on all traces of length n, then bounded bisimulation holds at depth n.
-/

import FormalVerification.Runner

/--
  **Soundness of lockstep testing.**
  If the test runner passes on all action traces of length n
  (i.e., bridge_equiv holds at each step for every possible trace),
  then bounded bisimulation holds at depth n.
-/
theorem lockstep_test_sound (sys : LockstepSystem) (n : Nat)
    (sm₀ : sys.SM) (ss₀ : sys.SS)
    (h : ∀ (trace : List sys.ActionIdx), trace.length = n →
         runner_passes sys trace sm₀ ss₀) :
    bounded_bisim sys n sm₀ ss₀ :=
  (runner_bounded_bisim_equiv sys n sm₀ ss₀).mp h

/-- Deeper tests give strictly stronger guarantees. -/
theorem deeper_test_stronger (sys : LockstepSystem) (sm : sys.SM) (ss : sys.SS)
    (n m : Nat) (h : n ≤ m) :
    bounded_bisim sys m sm ss → bounded_bisim sys n sm ss :=
  bounded_bisim_mono sys n m sm ss h

/-- Transparent bridge equivalence is just equality. -/
theorem transparent_equiv_is_eq (T : Type) [DecidableEq T] (r m : T) :
    bridge_equiv (transparent T) r m ↔ r = m := by
  unfold bridge_equiv transparent
  simp [id]

/-- Opaque bridge equivalence is trivially true. -/
theorem opaque_equiv_trivial (R M : Type) (r : R) (m : M) :
    bridge_equiv (opaqueBridge R M) r m :=
  opaqueBridge_always R M r m

/--
  **Depth increases strength.**
  Testing at depth m ≥ n gives a strictly stronger guarantee than
  testing at depth n. At sufficient depth (for finite-state models),
  the bounded bisimulation converges to the full bisimulation.
-/
theorem testing_depth_increases_strength
    (sys : LockstepSystem) (sm : sys.SM) (ss : sys.SS)
    (n : Nat) (hbisim : bounded_bisim sys (n + 1) sm ss) :
    bounded_bisim sys n sm ss :=
  bounded_bisim_mono sys n (n + 1) sm ss (Nat.le_succ n) hbisim
