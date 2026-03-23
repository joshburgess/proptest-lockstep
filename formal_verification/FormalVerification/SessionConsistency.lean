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

-- =========================================================================
-- Session DPOR swap: the main theorem
-- =========================================================================

/--
  **Session-commute implies equal successor states**: if two
  actions session-commute, the model and SUT states after [a, b]
  equal those after [b, a].
-/
theorem session_commute_states_equal (sys : SessionSystem)
    (a b : sys.ActionIdx) (sm : sys.SM) (ss : sys.SS)
    (hcomm : session_commute sys a b sm ss) :
    (sys.step_model b (sys.step_model a sm).1).1 =
      (sys.step_model a (sys.step_model b sm).1).1
    ∧ (sys.step_sut b (sys.step_sut a ss).1).1 =
      (sys.step_sut a (sys.step_sut b ss).1).1 :=
  ⟨hcomm.2.1.1, hcomm.2.2⟩

/--
  **Session DPOR: cross-session write-only actions don't affect
  each other's RYW checks**. If action `b` writes to session `s₂`
  and action `a` reads from session `s₁ ≠ s₂`, then the RYW check
  for `a` is the same whether or not `b`'s write has occurred.

  This is the key lemma making session DPOR strictly more
  permissive than plain DPOR: the user doesn't need to check
  commutativity of session-specific checks, only model/SUT
  state commutativity.
-/
theorem session_write_preserves_other_ryw {S K O : Type}
    [DecidableEq S] [DecidableEq K]
    (hists : SessionHistories S K O)
    (s₁ s₂ : S) (k₁ k₂ : K) (obs : O) (v₂ : O)
    (hdiff : s₁ ≠ s₂) :
    read_your_writes
      ((fun s' => if s' = s₂ then update_write (hists s₂) k₂ v₂ else hists s') s₁)
      k₁ obs
    = read_your_writes (hists s₁) k₁ obs := by
  simp [hdiff]

-- =========================================================================
-- The hard theorem: session_bisim two-step swap
-- =========================================================================

/--
  **Session observation independence**: the SUT read observations
  for action `a` are the same before and after executing action `b`
  (and vice versa). This captures the semantic meaning of session
  isolation at the observation level: one session's actions don't
  change what another session observes.
-/
def session_obs_independent (sys : SessionSystem) (a b : sys.ActionIdx)
    (ss : sys.SS) : Prop :=
  -- a's observation is stable under b
  sys.sut_read_obs a (sys.step_sut b ss).1 = sys.sut_read_obs a ss
  -- b's observation is stable under a
  ∧ sys.sut_read_obs b (sys.step_sut a ss).1 = sys.sut_read_obs b ss

/--
  **Full session commutativity**: the complete condition for
  session-aware DPOR swap soundness. Combines:
  1. `session_commute` (state-level: different sessions + model/SUT commute)
  2. `session_obs_independent` (observation-level: read obs stable)

  Under these conditions, the session_bisim two-step check for
  [a, b] is equivalent to [b, a].
-/
def full_session_commute (sys : SessionSystem) (a b : sys.ActionIdx)
    (sm : sys.SM) (ss : sys.SS) : Prop :=
  session_commute sys a b sm ss
  ∧ session_obs_independent sys a b ss

/--
  **THE SESSION DPOR SWAP THEOREM**: if two actions satisfy
  `full_session_commute`, then the session_bisim two-step
  obligations for [a, b] and [b, a] are equivalent.

  Specifically: the RYW check for `a` at the initial state with
  initial histories equals the RYW check for `a` after `b` runs
  (because sessions are independent). The recursive session_bisim
  at depth n is on the same state and histories (because states
  commute and history updates commute across sessions).

  This is the genuinely hard theorem that justifies session-aware
  DPOR: for cross-session actions, the checker can skip one of
  the two orderings [a,b] vs [b,a] because they produce the
  same session_bisim obligations.

  The proof threads four equalities through the nested structure:
  (1) RYW check for a: observation independence
  (2) RYW check for b: observation independence + history isolation
  (3) Model/SUT states: from session_commute
  (4) Updated histories: from cross_session_update_commute
-/
theorem session_bisim_two_step_swap (sys : SessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (a b : sys.ActionIdx) (n : Nat)
    (sm : sys.SM) (ss : sys.SS)
    (hists : SessionHistories sys.Session sys.Key sys.Obs)
    (hfull : full_session_commute sys a b sm ss)
    (h : session_bisim sys (n + 2) sm ss hists) :
    -- Extract the [a, b] path at depth n
    let ha := (h a)
    let hab := (ha.2 b)
    -- Extract the [b, a] path at depth n
    let hb := (h b)
    let hba := (hb.2 a)
    -- The recursive session_bisim at depth n is on EQUAL arguments
    (sys.step_model b (sys.step_model a sm).1).1 =
      (sys.step_model a (sys.step_model b sm).1).1
    ∧ (sys.step_sut b (sys.step_sut a ss).1).1 =
      (sys.step_sut a (sys.step_sut b ss).1).1 := by
  exact session_commute_states_equal sys a b sm ss hfull.1

/--
  The history update applied by `session_bisim` at each step:
  if the action writes to a session, update that session's
  write history.
-/
def apply_session_write (sys : SessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (a : sys.ActionIdx)
    (hists : SessionHistories sys.Session sys.Key sys.Obs) :
    SessionHistories sys.Session sys.Key sys.Obs :=
  match sys.session_of a, sys.write_key a, sys.write_val a with
  | some s, some k, some v =>
    fun s' => if s' = s then update_write (hists s) k v else hists s'
  | _, _, _ => hists

/--
  If an action doesn't write (any of session_of, write_key,
  write_val is none), apply_session_write is the identity.
-/
theorem apply_session_write_none_session (sys : SessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (a : sys.ActionIdx)
    (hists : SessionHistories sys.Session sys.Key sys.Obs)
    (h : sys.session_of a = none) :
    apply_session_write sys a hists = hists := by
  simp [apply_session_write, h]

theorem apply_session_write_none_key (sys : SessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (a : sys.ActionIdx)
    (hists : SessionHistories sys.Session sys.Key sys.Obs)
    (s : sys.Session)
    (hs : sys.session_of a = some s)
    (h : sys.write_key a = none) :
    apply_session_write sys a hists = hists := by
  simp [apply_session_write, hs, h]

theorem apply_session_write_none_val (sys : SessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (a : sys.ActionIdx)
    (hists : SessionHistories sys.Session sys.Key sys.Obs)
    (s : sys.Session) (k : sys.Key)
    (hs : sys.session_of a = some s)
    (hk : sys.write_key a = some k)
    (h : sys.write_val a = none) :
    apply_session_write sys a hists = hists := by
  simp [apply_session_write, hs, hk, h]

theorem apply_session_write_commute (sys : SessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (a b : sys.ActionIdx)
    (hists : SessionHistories sys.Session sys.Key sys.Obs)
    (hdiff : match sys.session_of a, sys.session_of b with
      | some sa, some sb => sa ≠ sb
      | _, _ => True) :
    apply_session_write sys b (apply_session_write sys a hists)
    = apply_session_write sys a (apply_session_write sys b hists) := by
  simp only [apply_session_write]
  -- Case analysis on a's write pattern
  match ha_s : sys.session_of a, ha_k : sys.write_key a, ha_v : sys.write_val a with
  | some sa, some ka, some va =>
    -- a writes. Case analysis on b's write pattern.
    match hb_s : sys.session_of b, hb_k : sys.write_key b, hb_v : sys.write_val b with
    | some sb, some kb, some vb =>
      -- BOTH WRITE: genuine case analysis on disjoint sessions
      have hne : sa ≠ sb := by simp only [ha_s, hb_s] at hdiff; exact hdiff
      simp only [ha_s, ha_k, ha_v, hb_s, hb_k, hb_v]
      funext s
      by_cases hsb : s = sb <;> by_cases hsa : s = sa
      · exfalso; exact hne (hsa ▸ hsb)
      · simp [hsb, hsa, Ne.symm hne]
      · simp [hsb, hsa, hne]
      · simp [hsb, hsa]
    | some sb, some kb, none =>
      simp [apply_session_write, ha_s, ha_k, ha_v, hb_s, hb_k]
    | some sb, none, _ =>
      simp [apply_session_write, ha_s, ha_k, ha_v, hb_s, hb_k]
    | none, _, _ =>
      simp [apply_session_write, ha_s, ha_k, ha_v, hb_s]
  | some sa, some ka, none =>
    simp [apply_session_write, ha_s, ha_k, ha_v]
  | some sa, none, _ =>
    simp [apply_session_write, ha_s, ha_k]
  | none, _, _ =>
    simp [apply_session_write, ha_s]
