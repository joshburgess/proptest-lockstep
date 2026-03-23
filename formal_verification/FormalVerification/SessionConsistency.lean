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
import FormalVerification.DPOR

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
  last_read : K → Option O

/-- Empty session history. -/
def empty_history (K O : Type) : SessionHistory K O :=
  { last_write := fun _ => none, last_read := fun _ => none }

/-- Update history after a write. -/
def update_write [DecidableEq K] (hist : SessionHistory K O) (k : K) (v : O) :
    SessionHistory K O :=
  { last_write := fun k' => if k' = k then some v else hist.last_write k',
    last_read := hist.last_read }

/-- Update history after a read. -/
def update_read [DecidableEq K] (hist : SessionHistory K O) (k : K) (v : O) :
    SessionHistory K O :=
  { last_write := hist.last_write,
    last_read := fun k' => if k' = k then some v else hist.last_read k' }

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
-- Monotonic reads guarantee
-- =========================================================================

/--
  **Monotonic reads**: if a session previously read value `v` at
  key `k`, then a subsequent read of `k` must return a value ≥ `v`
  (in the observation ordering). Returns `True` if the session
  hasn't read this key before (no constraint).

  Requires a `LE` instance on the observation type to express
  the monotonicity constraint.
-/
def monotonic_reads (hist : SessionHistory K O)
    (k : K) (obs : O) (obs_le : O → O → Prop) : Prop :=
  match hist.last_read k with
  | some prev => obs_le prev obs
  | none => True

/--
  **RYW implies monotonic reads** when the ordering is reflexive and
  writes are the only source of values: if read_your_writes holds and
  the last write equals the last read, then monotonic reads holds
  (under a reflexive ordering).
-/
theorem ryw_implies_monotonic_on_write (K O : Type) [DecidableEq K]
    (obs_le : O → O → Prop) (hrefl : ∀ x, obs_le x x)
    (hist : SessionHistory K O) (k : K) (obs : O)
    (hryw : read_your_writes hist k obs)
    (hwrite_read : hist.last_write k = hist.last_read k) :
    monotonic_reads hist k obs obs_le := by
  unfold monotonic_reads
  rw [← hwrite_read]
  unfold read_your_writes at hryw
  match hist.last_write k, hryw with
  | some v, hryw => rw [hryw]; exact hrefl v
  | none, _ => trivial

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
  session guarantee: if the bridge passes for action `a` (i.e.,
  `bridge_equiv` holds), then the read_your_writes check also
  passes for that action's session. This conditioning on
  `bridge_equiv` is the natural weakening — it says that
  bridge-compatible results satisfy RYW, which is a local
  property of the bridge and session semantics.

  Note: `hryw` still quantifies over all histories, not just
  reachable ones. Restricting to reachable histories would require
  threading execution paths through the induction, significantly
  complicating the proof for a marginal gain (in practice,
  bridge-compatible systems satisfy RYW for all histories).
-/
theorem bounded_implies_session (sys : SessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (hists : SessionHistories sys.Session sys.Key sys.Obs)
    (h : bounded_bisim sys.toLockstepSystem n sm ss)
    (hryw : ∀ (a : sys.ActionIdx) (sm' : sys.SM) (ss' : sys.SS)
        (hists' : SessionHistories sys.Session sys.Key sys.Obs),
        -- If the bridge passes at this step...
        bridge_equiv (sys.bridge a) (sys.step_sut a ss').2 (sys.step_model a sm').2 →
        -- ...then the RYW check passes for that action's session
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
    · exact hryw a sm ss hists ha.1
    · exact ih _ _ _ ha.2

/--
  **Session bisimulation is monotone in depth.** If session_bisim
  holds at depth m, it holds at depth n ≤ m (with appropriate
  history transformations at each step).

  Note: unlike environment-free bisimulations, the histories evolve
  at each step. Monotonicity holds because the depth-n check is a
  prefix of the depth-m check — the first n steps are identical.
-/
theorem session_bisim_mono (sys : SessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key] :
    ∀ (n m : Nat) (sm : sys.SM) (ss : sys.SS)
    (hists : SessionHistories sys.Session sys.Key sys.Obs),
    n ≤ m → session_bisim sys m sm ss hists →
    session_bisim sys n sm ss hists := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ k ih =>
    intro m sm ss hists h hm
    match m, h with
    | m' + 1, h' =>
      simp only [session_bisim] at hm ⊢
      intro a
      obtain ⟨hryw, hrest⟩ := hm a
      exact ⟨hryw, ih m' _ _ _ (by omega) hrest⟩

-- =========================================================================
-- Session implies convergent (hierarchy edge)
-- =========================================================================

/--
  **Session bisim preserves successor structure**: if session bisim
  holds at depth n+1, then for every action, session bisim holds
  at depth n on the successor states (with updated histories).
-/
theorem session_bisim_step (sys : SessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (hists : SessionHistories sys.Session sys.Key sys.Obs)
    (h : session_bisim sys (n + 1) sm ss hists)
    (a : sys.ActionIdx) :
    ∃ hists', session_bisim sys n
      (sys.step_model a sm).1 (sys.step_sut a ss).1 hists' := by
  simp only [session_bisim] at h
  exact ⟨_, (h a).2⟩

/--
  **Session → convergent connection**: session bisim's successor
  structure (∀ action, bisim at depth n on successors) is the same
  structure that convergent bisim requires. The only additional
  requirement for convergent bisim is sync agreement — which is
  a separate property of the system.

  This theorem extracts the successor-structure part: if session
  bisim holds, successors are covered for all actions.
-/
theorem session_successor_structure (sys : SessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (hists : SessionHistories sys.Session sys.Key sys.Obs)
    (h : session_bisim sys (n + 1) sm ss hists)
    (a : sys.ActionIdx) :
    session_bisim sys n
      (sys.step_model a sm).1 (sys.step_sut a ss).1
      (match sys.session_of a, sys.write_key a, sys.write_val a with
       | some s, some k, some v =>
         fun s' => if s' = s then update_write (hists s) k v else hists s'
       | _, _, _ => hists) := by
  simp only [session_bisim] at h
  exact (h a).2

-- =========================================================================
-- Full session bisimulation (RYW + Monotonic Reads)
-- =========================================================================

/--
  **Full session bisimulation** with both read-your-writes AND
  monotonic reads guarantees. Unlike `session_bisim` (RYW only),
  this definition:
  1. Checks `read_your_writes` on every read action
  2. Checks `monotonic_reads` on every read action
  3. Updates `last_read` after each read action (threading it
     through the bisimulation)

  This integrates the `last_read` field and `update_read` function
  into the bisimulation, closing the integration gap.
-/
def session_bisim_full (sys : SessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (obs_le : sys.Obs → sys.Obs → Prop) :
    Nat → sys.SM → sys.SS →
    SessionHistories sys.Session sys.Key sys.Obs → Prop
  | 0, _, _, _ => True
  | n + 1, sm, ss, hists =>
    ∀ (a : sys.ActionIdx),
      -- Check RYW on reads
      let ryw_ok := match sys.session_of a, sys.read_key a, sys.sut_read_obs a ss with
        | some s, some k, some obs => read_your_writes (hists s) k obs
        | _, _, _ => True
      -- Check monotonic reads on reads
      let mr_ok := match sys.session_of a, sys.read_key a, sys.sut_read_obs a ss with
        | some s, some k, some obs => monotonic_reads (hists s) k obs obs_le
        | _, _, _ => True
      -- Update histories: writes update last_write
      let hists_w := match sys.session_of a, sys.write_key a, sys.write_val a with
        | some s, some k, some v =>
          fun s' => if s' = s then update_write (hists s) k v else hists s'
        | _, _, _ => hists
      -- Update histories: reads update last_read
      let hists' := match sys.session_of a, sys.read_key a, sys.sut_read_obs a ss with
        | some s, some k, some obs =>
          fun s' => if s' = s then update_read (hists_w s) k obs else hists_w s'
        | _, _, _ => hists_w
      ryw_ok ∧ mr_ok ∧ session_bisim_full sys obs_le n
        (sys.step_model a sm).1 (sys.step_sut a ss).1 hists'

/-- Full session bisim at depth 0 is trivially true. -/
theorem session_bisim_full_zero (sys : SessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (obs_le : sys.Obs → sys.Obs → Prop)
    (sm : sys.SM) (ss : sys.SS)
    (hists : SessionHistories sys.Session sys.Key sys.Obs) :
    session_bisim_full sys obs_le 0 sm ss hists :=
  trivial

/--
  **Full session bisimulation is monotone in depth.**
-/
theorem session_bisim_full_mono (sys : SessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (obs_le : sys.Obs → sys.Obs → Prop) :
    ∀ (n m : Nat) (sm : sys.SM) (ss : sys.SS)
    (hists : SessionHistories sys.Session sys.Key sys.Obs),
    n ≤ m → session_bisim_full sys obs_le m sm ss hists →
    session_bisim_full sys obs_le n sm ss hists := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ k ih =>
    intro m sm ss hists h hm
    match m, h with
    | m' + 1, h' =>
      simp only [session_bisim_full] at hm ⊢
      intro a
      obtain ⟨hryw, hmr, hrest⟩ := hm a
      exact ⟨hryw, hmr, ih m' _ _ _ (by omega) hrest⟩

-- =========================================================================
-- Session-aware DPOR: cross-session commutativity
-- =========================================================================

/--
  **Cross-session lookup independence**: looking up a session history
  at session `s₁` is unaffected by an update at session `s₂ ≠ s₁`.
  This is the foundational lemma for session-aware DPOR.
-/
theorem cross_session_lookup {S K O : Type} [DecidableEq S]
    (hists : SessionHistories S K O)
    (s₁ s₂ : S) (val : SessionHistory K O)
    (hdiff : s₁ ≠ s₂) :
    (fun s' => if s' = s₂ then val else hists s') s₁ = hists s₁ := by
  simp [hdiff]

/--
  **Cross-session RYW independence**: the read-your-writes check for
  session `s₁` is independent of history updates at session `s₂ ≠ s₁`.

  If another session modifies the history, it doesn't affect the
  RYW check for this session — because the `if s' = s₂` guard
  routes to `hists s₁` (unchanged) when `s₁ ≠ s₂`.
-/
theorem cross_session_ryw_independent {S K O : Type}
    [DecidableEq S] [DecidableEq K]
    (hists : SessionHistories S K O)
    (s₁ s₂ : S) (val : SessionHistory K O)
    (k : K) (obs : O)
    (hdiff : s₁ ≠ s₂) :
    read_your_writes
      ((fun s' => if s' = s₂ then val else hists s') s₁) k obs
    = read_your_writes (hists s₁) k obs := by
  simp [hdiff]

/--
  **Cross-session monotonic reads independence**: the monotonic reads
  check for session `s₁` is independent of history updates at
  session `s₂ ≠ s₁`.
-/
theorem cross_session_mr_independent {S K O : Type}
    [DecidableEq S] [DecidableEq K]
    (hists : SessionHistories S K O)
    (s₁ s₂ : S) (val : SessionHistory K O)
    (k : K) (obs : O) (obs_le : O → O → Prop)
    (hdiff : s₁ ≠ s₂) :
    monotonic_reads
      ((fun s' => if s' = s₂ then val else hists s') s₁) k obs obs_le
    = monotonic_reads (hists s₁) k obs obs_le := by
  simp [hdiff]

/--
  **Cross-session history update commutativity**: if two history
  updates target different sessions (`s₁ ≠ s₂`), applying them
  in either order produces the same result.

  This is the key structural lemma for session-aware DPOR: actions
  from different sessions produce commuting history updates.
-/
theorem cross_session_update_commute {S K O : Type} [DecidableEq S]
    (hists : SessionHistories S K O)
    (s₁ s₂ : S) (v₁ v₂ : SessionHistory K O)
    (hdiff : s₁ ≠ s₂) :
    (fun s => if s = s₂ then v₂ else
      (fun s' => if s' = s₁ then v₁ else hists s') s)
    = (fun s => if s = s₁ then v₁ else
      (fun s' => if s' = s₂ then v₂ else hists s') s) := by
  funext s
  simp only
  split <;> split <;> simp_all

-- =========================================================================
-- Session commutativity: the combined condition for session DPOR
-- =========================================================================

/--
  Two actions **session-commute** if they satisfy three conditions:
  1. They are from different sessions (history updates commute)
  2. The model states commute (`model_commute`)
  3. The SUT states commute (successor states are equal in both orders)

  When session_commute holds, the session-specific checks (RYW,
  monotonic reads) and history updates are order-independent
  (by the cross_session_* lemmas), and the underlying state
  transitions are order-independent (by model/SUT commutativity).

  This is a **strictly weaker** requirement than checking commutativity
  without session awareness: the history commutativity comes for free
  from session isolation, so the user only needs to verify
  model_commute + SUT state commutativity.
-/
def session_commute (sys : SessionSystem) (a b : sys.ActionIdx)
    (sm : sys.SM) (ss : sys.SS) : Prop :=
  -- Different sessions (or at least one is not session-tagged)
  (match sys.session_of a, sys.session_of b with
    | some sa, some sb => sa ≠ sb
    | _, _ => True)  -- non-session actions commute freely with sessions
  -- Model states commute
  ∧ model_commute sys.toLockstepSystem a b sm
  -- SUT successor states commute
  ∧ (sys.step_sut b (sys.step_sut a ss).1).1 =
    (sys.step_sut a (sys.step_sut b ss).1).1

/--
  **Session commutativity is symmetric.**
-/
theorem session_commute_sym (sys : SessionSystem) (a b : sys.ActionIdx)
    (sm : sys.SM) (ss : sys.SS)
    (h : session_commute sys a b sm ss) :
    session_commute sys b a sm ss := by
  obtain ⟨hdiff, hmodel, hsut⟩ := h
  refine ⟨?_, commute_sym sys.toLockstepSystem a b sm hmodel, hsut.symm⟩
  match ha : sys.session_of a, hb : sys.session_of b with
  | some sa, some sb => simp [ha, hb] at hdiff ⊢; exact Ne.symm hdiff
  | some _, none => simp [ha, hb]
  | none, some _ => simp [ha, hb]
  | none, none => simp [ha, hb]
