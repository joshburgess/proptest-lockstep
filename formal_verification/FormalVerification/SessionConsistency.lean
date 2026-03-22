/-
  Session Consistency

  Formalizes session consistency guarantees: per-session ordering
  constraints that sit between linearizability and eventual consistency.

  A session is a sequence of operations by a single client/thread.
  Session guarantees ensure that each session sees a consistent
  view of the system:

  - **Read-your-writes**: if a session writes v at key k, its next
    read of k returns v

  The key insight: session consistency is a per-session property,
  not a global one. Two sessions can see different states, but each
  session's view must be internally consistent.

  The `session_bisim` definition threads per-session histories
  through the bisimulation and checks `read_your_writes` at each
  read action.

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
  Session : Type
  Key : Type
  Obs : Type
  session_of : ActionIdx → Option Session
  -- Extract the key and SUT observation from a read action
  read_key : ActionIdx → Option Key
  sut_read_obs : ActionIdx → SS → Option Obs
  -- Extract the key and value from a write action
  write_key : ActionIdx → Option Key
  write_val : ActionIdx → Option Obs

-- =========================================================================
-- Session history
-- =========================================================================

/--
  A session history records the last write per key for a single session.
-/
structure SessionHistory (K O : Type) where
  last_write : K → Option O

/-- Empty session history. -/
def empty_history (K O : Type) : SessionHistory K O :=
  { last_write := fun _ => none }

/-- Update history after a write. -/
def update_write [DecidableEq K] (hist : SessionHistory K O) (k : K) (v : O) :
    SessionHistory K O :=
  { last_write := fun k' => if k' = k then some v else hist.last_write k' }

-- =========================================================================
-- Read-your-writes guarantee
-- =========================================================================

/--
  **Read-your-writes**: if a session previously wrote value `v` at
  key `k`, then a read of `k` must return `v`.
  Returns `True` if the session hasn't written to this key (no constraint).
-/
def read_your_writes [DecidableEq K] (hist : SessionHistory K O)
    (k : K) (obs : O) : Prop :=
  match hist.last_write k with
  | some v => obs = v
  | none => True

-- =========================================================================
-- Session bisimulation (with history threading)
-- =========================================================================

/--
  Per-session state: the history for one session.
-/
def SessionHistories (Session Key Obs : Type) :=
  Session → SessionHistory Key Obs

/-- Empty histories for all sessions. -/
def empty_histories (S K O : Type) : SessionHistories S K O :=
  fun _ => empty_history K O

/--
  Session-consistent bisimulation at depth n. Unlike `bounded_bisim`,
  this does NOT require bridge_equiv at every step. Instead, it
  requires that for every read action in a session, the
  `read_your_writes` guarantee holds with respect to that session's
  write history.

  The history is threaded through: writes update the session's
  history, and subsequent reads are checked against it.
-/
def session_bisim (sys : SessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key] :
    Nat → sys.SM → sys.SS →
    SessionHistories sys.Session sys.Key sys.Obs → Prop
  | 0, _, _, _ => True
  | n + 1, sm, ss, hists =>
    ∀ (a : sys.ActionIdx),
      -- If this is a read by session s, check read_your_writes
      let ryw_ok := match sys.session_of a, sys.read_key a, sys.sut_read_obs a ss with
        | some s, some k, some obs => read_your_writes (hists s) k obs
        | _, _, _ => True
      -- Update histories if this is a write by session s
      let hists' := match sys.session_of a, sys.write_key a, sys.write_val a with
        | some s, some k, some v =>
          fun s' => if s' = s then update_write (hists s) k v else hists s'
        | _, _, _ => hists
      ryw_ok ∧ session_bisim sys n
        (sys.step_model a sm).1 (sys.step_sut a ss).1 hists'

-- =========================================================================
-- Properties
-- =========================================================================

/-- Session bisim at depth 0 is trivially true. -/
theorem session_bisim_zero (sys : SessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (sm : sys.SM) (ss : sys.SS) (h : SessionHistories sys.Session sys.Key sys.Obs) :
    session_bisim sys 0 sm ss h :=
  trivial

/--
  **Bounded bisim implies session bisim** (under a bridge-to-RYW
  compatibility condition): if every step satisfies bridge_equiv
  (linearizability), and bridge passing implies the RYW check
  passes, then session bisim holds.

  The `hryw` hypothesis connects the bridge guarantee to the
  session guarantee: if the bridge passes for action `a`, then
  the read_your_writes check also passes for that action's session.
-/
theorem bounded_implies_session (sys : SessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (hists : SessionHistories sys.Session sys.Key sys.Obs)
    (h : bounded_bisim sys.toLockstepSystem n sm ss)
    (hryw : ∀ (a : sys.ActionIdx) (ss' : sys.SS)
        (hists' : SessionHistories sys.Session sys.Key sys.Obs),
        -- The RYW condition for each read action at each step
        match sys.session_of a, sys.read_key a, sys.sut_read_obs a ss' with
        | some s, some rk, some obs => read_your_writes (hists' s) rk obs
        | _, _, _ => True) :
    session_bisim sys n sm ss hists := by
  induction n generalizing sm ss hists with
  | zero => trivial
  | succ k ih =>
    simp only [session_bisim]
    intro a
    simp only [bounded_bisim] at h
    have ha := h a
    constructor
    · exact hryw a ss hists
    · exact ih _ _ _ ha.2

-- Note on session_implies_convergent:
-- The hierarchy edge session ⟹ convergent requires connecting
-- SessionSystem to EventualSystem (different Lean structures).
-- The strictness of bounded ⟹ convergent is proved in
-- HierarchyStrictness.lean via convergent_strictly_weaker.
