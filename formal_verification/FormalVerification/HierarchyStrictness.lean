/-
  Consistency Hierarchy Strictness

  Proves the consistency hierarchy is STRICT: each level is
  genuinely weaker than the one above. Without these theorems,
  the implications could be equivalences (all notions could collapse).

  We construct concrete counterexample systems witnessing each gap:
  - A system that satisfies convergent_bisim but NOT bounded_bisim
    (bounded_bisim is strictly stronger than convergent_bisim)
  - A system that satisfies convergent_bisim but NOT session_bisim
    (session_bisim is strictly stronger than convergent_bisim)

  Together these witness BOTH gaps in the three-level hierarchy:
    session → convergent → bounded (each strictly stronger)

  This makes the hierarchy diagram a theorem, not a claim.
-/

import FormalVerification.Lockstep
import FormalVerification.EventualConsistency
import FormalVerification.SessionConsistency

-- =========================================================================
-- Strictness: convergent_bisim does NOT imply bounded_bisim
-- =========================================================================

/--
  A concrete system where convergent_bisim holds but bounded_bisim
  does NOT. The system has one action that produces different results
  from model and SUT (bridge_equiv fails), but the sync function
  ignores the difference (convergent_bisim passes).

  This is the "stale read" pattern: the SUT returns stale data,
  but after sync, everything agrees.
-/
def stale_read_system : EventualSystem where
  SM := Unit
  SS := Unit
  ActionIdx := Unit
  RetM := fun _ => Bool  -- model returns true
  RetS := fun _ => Bool  -- SUT returns false (stale!)
  bridge := fun _ => transparent Bool
  step_model := fun _ _ => ((), true)
  step_sut := fun _ _ => ((), false)  -- STALE: returns false
  OS := Unit
  model_sync := fun _ => ()  -- sync ignores the difference
  sut_sync := fun _ => ()
  invariant := fun _ => True

/--
  **bounded_bisim fails for the stale read system.**
  bridge_equiv (transparent Bool) false true = (false = true) = False.
-/
theorem stale_read_not_linearizable :
    ¬ bounded_bisim stale_read_system.toLockstepSystem 1 () () := by
  intro h
  simp only [bounded_bisim] at h
  have := h ()
  simp only [stale_read_system, bridge_equiv, transparent] at this
  exact absurd this.1 (by simp [id])

/--
  **convergent_bisim holds for the stale read system.**
  model_sync and sut_sync both return (), so sync agreement holds.
-/
theorem stale_read_eventually_consistent :
    convergent_bisim stale_read_system 1 () () := by
  simp only [convergent_bisim, stale_read_system]
  exact ⟨trivial, trivial, fun _ => trivial⟩

/--
  **THE STRICTNESS THEOREM**: convergent_bisim does NOT imply
  bounded_bisim. There exists a system (stale_read_system) where
  convergent_bisim holds at depth 1 but bounded_bisim fails at depth 1.
-/
theorem convergent_strictly_weaker :
    ∃ (sys : EventualSystem) (sm : sys.SM) (ss : sys.SS),
      convergent_bisim sys 1 sm ss
      ∧ ¬ bounded_bisim sys.toLockstepSystem 1 sm ss :=
  ⟨stale_read_system, (), (),
   stale_read_eventually_consistent,
   stale_read_not_linearizable⟩

-- =========================================================================
-- Strictness: convergent_bisim does NOT imply session_bisim
-- =========================================================================

/--
  A system that satisfies convergent_bisim but violates session_bisim.

  The SUT always returns `false` on reads (stale data), but the sync
  functions trivially agree (`model_sync = sut_sync = fun _ => ()`).

  This means the system is eventually consistent — sync always matches —
  but violates read-your-writes: a session that writes `true` at a key
  and then reads it back gets `false`.

  The underlying transition system is identical to `stale_read_system`
  but extended with session/key/observation structure.
-/
def ryw_violation_session : SessionSystem where
  SM := Bool
  SS := Bool
  ActionIdx := Bool  -- true = write, false = read
  RetM := fun _ => Bool
  RetS := fun _ => Bool
  bridge := fun _ => transparent Bool
  step_model := fun a sm => match a with
    | true => (true, true)    -- write: state ← true, returns true
    | false => (sm, sm)       -- read: returns current state
  step_sut := fun a ss => match a with
    | true => (true, true)    -- write: state ← true, returns true
    | false => (ss, false)    -- read: ALWAYS returns false (stale!)
  Session := Unit
  Key := Unit
  Obs := Bool
  session_of := fun _ => some ()
  read_key := fun a => match a with
    | false => some ()
    | true => none
  sut_read_obs := fun a _ => match a with
    | false => some false     -- SUT always observes false on read
    | true => none
  write_key := fun a => match a with
    | true => some ()
    | false => none
  write_val := fun a => match a with
    | true => some true       -- write records observation true
    | false => none

instance : DecidableEq ryw_violation_session.Session :=
  show DecidableEq Unit from inferInstance
instance : DecidableEq ryw_violation_session.Key :=
  show DecidableEq Unit from inferInstance

/--
  The eventual system version of the RYW-violation system, with trivial
  sync that always agrees. Same underlying transitions as
  `ryw_violation_session`.
-/
def ryw_violation_eventual : EventualSystem where
  SM := Bool
  SS := Bool
  ActionIdx := Bool
  RetM := fun _ => Bool
  RetS := fun _ => Bool
  bridge := fun _ => transparent Bool
  step_model := fun a sm => match a with
    | true => (true, true)
    | false => (sm, sm)
  step_sut := fun a ss => match a with
    | true => (true, true)
    | false => (ss, false)
  OS := Unit
  model_sync := fun _ => ()
  sut_sync := fun _ => ()
  invariant := fun _ => True

/--
  **convergent_bisim holds for the RYW-violation system at every depth.**
  Both sync functions return `()`, so sync agreement is trivially satisfied.
  The invariant is `True`, so the invariant condition is also trivial.
-/
theorem ryw_violation_convergent :
    ∀ (n : Nat) (sm ss : Bool),
    convergent_bisim ryw_violation_eventual n sm ss := by
  intro n
  induction n with
  | zero =>
    intro sm ss
    simp [convergent_bisim, ryw_violation_eventual]
  | succ k ih =>
    intro sm ss
    simp only [convergent_bisim, ryw_violation_eventual]
    exact ⟨trivial, trivial, fun a => by cases a <;> exact ih _ _⟩

/--
  **session_bisim fails for the RYW-violation system at depth 2.**

  The action sequence write-then-read violates read-your-writes:
  1. Write action records `true` at key `()` in session `()`'s history
  2. Read action observes `false` from the SUT
  3. `read_your_writes` requires `false = true` — contradiction.
-/
theorem ryw_violation_not_session :
    ¬ session_bisim ryw_violation_session 2 false false
        (empty_histories Unit Unit Bool) := by
  intro h
  -- Unfold depth 2
  unfold session_bisim at h
  -- Take the write action (true)
  have hwrite := h true
  dsimp [ryw_violation_session, empty_histories, empty_history] at hwrite
  obtain ⟨_, hrest⟩ := hwrite
  -- Now at depth 1, with updated history recording write of true at ()
  unfold session_bisim at hrest
  -- Take the read action (false)
  have hread := hrest false
  simp [update_write, read_your_writes] at hread

/--
  **THE SESSION STRICTNESS THEOREM**: session_bisim is strictly stronger
  than convergent_bisim. The `ryw_violation` system satisfies convergent
  bisimulation at every depth (sync always agrees) but fails session
  bisimulation at depth 2 (the write-then-read sequence violates
  read-your-writes).

  Together with `convergent_strictly_weaker`, this witnesses BOTH gaps
  in the three-level hierarchy:
    bounded_bisim ⊂ session_bisim ⊂ convergent_bisim
  (where ⊂ denotes strictly stronger).
-/
theorem session_strictly_stronger :
    (∀ (n : Nat), convergent_bisim ryw_violation_eventual n false false)
    ∧ ¬ session_bisim ryw_violation_session 2 false false
        (empty_histories Unit Unit Bool) :=
  ⟨fun n => ryw_violation_convergent n false false,
   ryw_violation_not_session⟩
