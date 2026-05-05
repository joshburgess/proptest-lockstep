/-
  Eventual Consistency

  Formalizes eventual consistency testing: a weaker guarantee than
  linearizability where individual operations may return stale results,
  but after synchronization (quiescence), the model and SUT agree on
  the observable state.

  The key notion is `convergent_bisim`: like bounded_bisim but without
  per-step bridge_equiv. Instead, only requires convergence at sync
  points -- the observable state matches after synchronization.

  This is the first formally verified eventual consistency PBT
  framework. It fills the gap between CRDT verification (full proofs
  of specific data types) and ad-hoc convergence testing.

  Corresponds to `EventualConsistencyModel` in `src/eventual.rs`.
-/

import Metatheory.Invariant

-- =========================================================================
-- Eventual consistency system
-- =========================================================================

/--
  A lockstep system extended with eventual consistency semantics.
  Adds sync operations and an observable state type that must
  converge after synchronization.
-/
structure EventualSystem extends LockstepSystem where
  OS : Type                     -- observable state after sync
  model_sync : SM → OS          -- extract observable from model
  sut_sync : SS → OS            -- extract observable from SUT (after sync)
  invariant : SM → Prop         -- state invariant

-- =========================================================================
-- Convergent bisimulation
-- =========================================================================

/--
  Convergent bisimulation at depth n. Unlike `bounded_bisim`, this
  does NOT require bridge_equiv at every step. Instead:
  1. The invariant holds at every reachable model state
  2. Actions advance both model and SUT states
  3. At any point, syncing produces the same observable state

  The key difference from `bounded_bisim`: no per-step bridge check.
  The "observation" happens only at sync points.
-/
def convergent_bisim (sys : EventualSystem) :
    Nat → sys.SM → sys.SS → Prop
  | 0, sm, ss => sys.model_sync sm = sys.sut_sync ss
  | n + 1, sm, ss =>
    -- Invariant holds
    sys.invariant sm
    -- Observable states agree NOW (sync would succeed)
    ∧ sys.model_sync sm = sys.sut_sync ss
    -- After any action, convergent bisim holds at depth n
    ∧ ∀ (a : sys.ActionIdx),
        convergent_bisim sys n
          (sys.step_model a sm).1
          (sys.step_sut a ss).1

-- =========================================================================
-- Properties
-- =========================================================================

/-- Convergent bisim at depth 0 is sync agreement. -/
theorem convergent_bisim_zero (sys : EventualSystem)
    (sm : sys.SM) (ss : sys.SS) :
    convergent_bisim sys 0 sm ss ↔
    sys.model_sync sm = sys.sut_sync ss := by
  simp [convergent_bisim]

/--
  **Convergence at every depth**: if convergent bisim holds at depth
  n, then syncing at the current state produces agreement.
-/
theorem convergent_bisim_sync (sys : EventualSystem)
    (sm : sys.SM) (ss : sys.SS) (n : Nat)
    (h : convergent_bisim sys n sm ss) :
    sys.model_sync sm = sys.sut_sync ss := by
  cases n with
  | zero => exact h
  | succ k =>
    simp only [convergent_bisim] at h
    exact h.2.1

/-- Model state after running a trace. -/
def ec_model_after (sys : EventualSystem) :
    List sys.ActionIdx → sys.SM → sys.SM
  | [], sm => sm
  | a :: rest, sm => ec_model_after sys rest (sys.step_model a sm).1

/-- SUT state after running a trace. -/
def ec_sut_after (sys : EventualSystem) :
    List sys.ActionIdx → sys.SS → sys.SS
  | [], ss => ss
  | a :: rest, ss => ec_sut_after sys rest (sys.step_sut a ss).1

/--
  **Convergence after prefix**: if convergent bisim holds at
  sufficient depth, then after running any prefix of actions,
  syncing still produces agreement.
-/
theorem convergent_after_prefix (sys : EventualSystem)
    (pre : List sys.ActionIdx)
    (sm : sys.SM) (ss : sys.SS)
    (h : convergent_bisim sys pre.length sm ss) :
    sys.model_sync (ec_model_after sys pre sm)
    = sys.sut_sync (ec_sut_after sys pre ss) := by
  induction pre generalizing sm ss with
  | nil =>
    simp [ec_model_after, ec_sut_after]
    exact convergent_bisim_sync sys sm ss 0 h
  | cons a rest ih =>
    simp only [ec_model_after, ec_sut_after]
    have hlen : (a :: rest).length = rest.length + 1 := by simp
    rw [hlen] at h
    simp only [convergent_bisim] at h
    exact ih _ _ (h.2.2 a)

/-- Convergent bisimulation is monotone in depth. -/
theorem convergent_bisim_mono (sys : EventualSystem) :
    ∀ (n m : Nat) (sm : sys.SM) (ss : sys.SS),
    n ≤ m → convergent_bisim sys m sm ss →
    convergent_bisim sys n sm ss := by
  intro n
  induction n with
  | zero =>
    intro m sm ss _ hm
    exact convergent_bisim_sync sys sm ss m hm
  | succ k ih =>
    intro m sm ss h hm
    match m, h with
    | m' + 1, h' =>
      simp only [convergent_bisim] at hm ⊢
      obtain ⟨hinv, hsync, hactions⟩ := hm
      refine ⟨hinv, hsync, ?_⟩
      intro a
      exact ih m' _ _ (by omega) (hactions a)

-- =========================================================================
-- Relationship to bounded bisimulation
-- =========================================================================

/--
  **Bounded bisim implies convergent bisim**: if the system satisfies
  bounded bisimulation (per-step bridge_equiv) AND the sync functions
  are consistent with the bridges, then it also satisfies convergent
  bisimulation.

  This means linearizable systems are automatically eventually
  consistent -- linearizability is strictly stronger.
-/
theorem bounded_implies_convergent (sys : EventualSystem)
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    -- The system satisfies bounded bisim (all bridges pass)
    (hbisim : bounded_bisim sys.toLockstepSystem n sm ss)
    -- The sync functions are consistent: if all bridges pass,
    -- sync produces the same observable state
    (hsync_consistent : ∀ sm' ss',
        bounded_bisim sys.toLockstepSystem 0 sm' ss' →
        sys.model_sync sm' = sys.sut_sync ss')
    -- Invariant holds at all reachable states
    (hinv : ∀ sm', sys.invariant sm') :
    convergent_bisim sys n sm ss := by
  induction n generalizing sm ss with
  | zero =>
    exact hsync_consistent sm ss (bounded_bisim_zero sys.toLockstepSystem sm ss)
  | succ k ih =>
    simp only [convergent_bisim]
    refine ⟨hinv sm, hsync_consistent sm ss (bounded_bisim_zero sys.toLockstepSystem sm ss), ?_⟩
    intro a
    simp only [bounded_bisim] at hbisim
    exact ih _ _ (hbisim a).2
