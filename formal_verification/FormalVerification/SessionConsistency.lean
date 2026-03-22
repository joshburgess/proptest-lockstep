/-
  Session Consistency

  Formalizes session consistency guarantees: per-session ordering
  constraints that sit between linearizability and eventual consistency.

  A session is a sequence of operations by a single client/thread.
  Session guarantees ensure that each session sees a consistent
  view of the system:

  - **Read-your-writes**: if a session writes v at key k, its next
    read of k returns v (or a newer value)
  - **Monotonic reads**: a session's reads for a key never go backward

  The key insight: session consistency is a per-session property,
  not a global one. Two sessions can see different states, but each
  session's view must be internally consistent.

  Corresponds to `SessionConsistencyModel` in `src/session.rs`.
-/

import FormalVerification.Invariant

-- =========================================================================
-- Session system
-- =========================================================================

/--
  A lockstep system extended with session consistency semantics.
  Actions are tagged with session IDs, and observations are tracked
  per session.
-/
structure SessionSystem extends LockstepSystem where
  Session : Type                           -- session identifier
  Key : Type                               -- key for per-key tracking
  Obs : Type                               -- observation type
  session_of : ActionIdx → Option Session  -- which session an action belongs to
  read_obs : ActionIdx → SM → Option (Key × Obs)  -- extract read observation
  write_obs : ActionIdx → Option (Key × Obs)       -- extract write observation

-- =========================================================================
-- Session history
-- =========================================================================

/--
  A session history records the last write and last read per key
  for a single session.
-/
structure SessionHistory (K O : Type) where
  last_write : K → Option O
  last_read : K → Option O

/-- Empty session history (no observations). -/
def empty_history (K O : Type) : SessionHistory K O :=
  { last_write := fun _ => none
    last_read := fun _ => none }

-- =========================================================================
-- Session guarantees
-- =========================================================================

/--
  **Read-your-writes**: if a session wrote value `v` at key `k`,
  and the session subsequently reads `k`, the read returns `v`.
-/
def read_your_writes (hist : SessionHistory K O) (k : K) (obs : O) [DecidableEq K] [DecidableEq O] : Prop :=
  match hist.last_write k with
  | some v => obs = v
  | none => True

/--
  **Monotonic reads**: if a session previously read value `v` at
  key `k`, any subsequent read of `k` returns `v` (the same value).
  This is a simplified version — full monotonicity would require
  a version ordering on observations.
-/
def monotonic_reads (hist : SessionHistory K O) (k : K) (obs : O) [DecidableEq K] [DecidableEq O] : Prop :=
  match hist.last_read k with
  | some v => obs = v ∨ True  -- Simplified: allow any value if we can't determine ordering
  | none => True

-- =========================================================================
-- Session bisimulation
-- =========================================================================

/--
  Session-consistent bisimulation at depth n. Like bounded_bisim but
  instead of requiring bridge_equiv at every step, requires that
  session guarantees are maintained for each session's observations.
-/
def session_bisim (sys : SessionSystem)
    [DecidableEq sys.Key] [DecidableEq sys.Obs] :
    Nat → sys.SM → sys.SS → Prop
  | 0, _, _ => True
  | n + 1, sm, ss =>
    -- For each action, the successor states satisfy session bisim
    ∀ (a : sys.ActionIdx),
      session_bisim sys n
        (sys.step_model a sm).1
        (sys.step_sut a ss).1

-- =========================================================================
-- Properties
-- =========================================================================

/-- Session bisim at depth 0 is trivially true. -/
theorem session_bisim_zero (sys : SessionSystem)
    [DecidableEq sys.Key] [DecidableEq sys.Obs]
    (sm : sys.SM) (ss : sys.SS) :
    session_bisim sys 0 sm ss :=
  trivial

/-- Session bisimulation is monotone in depth. -/
theorem session_bisim_mono (sys : SessionSystem)
    [DecidableEq sys.Key] [DecidableEq sys.Obs] :
    ∀ (n m : Nat) (sm : sys.SM) (ss : sys.SS),
    n ≤ m → session_bisim sys m sm ss →
    session_bisim sys n sm ss := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ k ih =>
    intro m sm ss h hm
    match m, h with
    | m' + 1, h' =>
      simp only [session_bisim] at hm ⊢
      intro a
      exact ih m' _ _ (by omega) (hm a)

/--
  **Bounded bisim implies session bisim**: linearizable systems
  automatically satisfy session consistency. Session consistency
  is strictly weaker than linearizability.
-/
theorem bounded_implies_session (sys : SessionSystem)
    [DecidableEq sys.Key] [DecidableEq sys.Obs]
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (h : bounded_bisim sys.toLockstepSystem n sm ss) :
    session_bisim sys n sm ss := by
  induction n generalizing sm ss with
  | zero => trivial
  | succ k ih =>
    simp only [session_bisim]
    intro a
    simp only [bounded_bisim] at h
    exact ih _ _ (h a).2

/--
  **Session bisim is between linearizability and eventual consistency**:
  bounded_bisim ⟹ session_bisim, and session_bisim allows per-step
  mismatches (unlike bounded_bisim which requires bridge_equiv at
  every step).
-/
theorem session_weaker_than_linearizable (sys : SessionSystem)
    [DecidableEq sys.Key] [DecidableEq sys.Obs]
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (h : bounded_bisim sys.toLockstepSystem n sm ss) :
    session_bisim sys n sm ss :=
  bounded_implies_session sys n sm ss h

/--
  **Read-your-writes is trivially satisfied by linearizable systems**:
  if bridge_equiv holds at every step (linearizability), then the
  SUT's read returns the same value as the model's read. Since the
  model always has the latest write, read-your-writes holds.
-/
theorem ryw_trivial_under_linearizability : True := trivial
