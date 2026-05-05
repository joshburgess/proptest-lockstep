/-
  Opaque Handle Detection

  Proves that opaque bridges -- which trivially pass at the point of
  return -- do not prevent detection of incorrect handles. A wrong
  opaque handle is caught when it is *used* by a subsequent action
  with a discriminating (e.g., transparent) bridge.

  The key insight: the bounded bisimulation's inductive structure
  ensures that passing at depth n requires passing at depth n-1 on
  successor states. An opaque bridge contributes nothing at its own
  step, but the successor-state requirement propagates the obligation
  forward to where a transparent bridge can detect the discrepancy.

  This formalizes the "delayed detection" property described in
  `theory.rs` under "Opacity and Behavioral Equivalence".
-/

import Metatheory.Runner

-- =========================================================================
-- Detection through successor states
-- =========================================================================

/--
  **Detection at successor**: if successor states (after running action a)
  fail bounded bisimulation at depth k, then the original states fail at
  depth k+1.

  This is the inductive mechanism that makes opaque handle detection work:
  even if the bridge at action a passes (as opaque bridges always do), the
  bisimulation at depth k+1 still fails because the successor states don't
  satisfy the depth-k requirement.
-/
theorem detection_at_successor (sys : LockstepSystem)
    (sm : sys.SM) (ss : sys.SS)
    (a : sys.ActionIdx) (k : Nat)
    (hfail : ¬ bounded_bisim sys k
        (sys.step_model a sm).1 (sys.step_sut a ss).1) :
    ¬ bounded_bisim sys (k + 1) sm ss := by
  intro hbisim
  simp only [bounded_bisim] at hbisim
  have ha := hbisim a
  exact hfail ha.2

/--
  **Failure propagates upward**: if bounded bisimulation fails at depth n,
  it fails at every depth m ≥ n. Contrapositive of `bounded_bisim_mono`.
-/
theorem failure_propagates_up (sys : LockstepSystem)
    (sm : sys.SM) (ss : sys.SS)
    (n m : Nat) (h : n ≤ m)
    (hfail : ¬ bounded_bisim sys n sm ss) :
    ¬ bounded_bisim sys m sm ss := by
  intro hbisim
  exact hfail (bounded_bisim_mono sys n m sm ss h hbisim)

-- =========================================================================
-- Opaque handle detection
-- =========================================================================

/--
  **Successor action detects discrepancy**: if action `b` at the
  successor states (after action `a`) detects a bridge discrepancy,
  then bounded bisimulation at depth 2 fails.

  This is the canonical "wrong opaque handle" scenario:
  1. Action `a` creates a handle -- opaque bridge passes trivially
  2. Action `b` uses the handle -- transparent bridge catches the error

  The theorem holds for any bridge on `a` (not just opaque), because
  the depth-2 bisimulation requires depth-1 bisimulation at successor
  states regardless of whether action `a`'s own bridge passes.
-/
theorem opaque_step_then_detect (sys : LockstepSystem)
    (sm : sys.SM) (ss : sys.SS) (a b : sys.ActionIdx)
    -- Action b detects a discrepancy at the successor states
    (hb_fails : ¬ bridge_equiv (sys.bridge b)
        (sys.step_sut b (sys.step_sut a ss).1).2
        (sys.step_model b (sys.step_model a sm).1).2) :
    ¬ bounded_bisim sys 2 sm ss := by
  intro hbisim
  simp only [bounded_bisim] at hbisim
  have ha := hbisim a
  have hsucc := ha.2 b
  exact hb_fails hsucc.1

/--
  **Delayed detection**: a discrepancy is detected at depth k+1 if the
  successor states (after action `a`) fail bisimulation at depth k.

  The bisimulation at depth k+1 requires depth k at successor states.
  If those successor states are distinguishable (by any sequence of k
  future actions with discriminating bridges), the depth-(k+1)
  bisimulation fails. This is `detection_at_successor` specialized
  to the delayed detection scenario.
-/
theorem opaque_delayed_detection (sys : LockstepSystem)
    (sm : sys.SM) (ss : sys.SS)
    (a : sys.ActionIdx) (k : Nat)
    -- Successor states are distinguishable at depth k
    (hfail : ¬ bounded_bisim sys k
        (sys.step_model a sm).1 (sys.step_sut a ss).1) :
    ¬ bounded_bisim sys (k + 1) sm ss :=
  detection_at_successor sys sm ss a k hfail

-- =========================================================================
-- Runner-level detection
-- =========================================================================

/--
  **Opaque runner failure is delayed**: if the runner fails on a trace
  starting with an opaque action, the failure must come from a later
  action in the trace -- the opaque step itself always passes.
-/
theorem opaque_runner_failure_is_delayed (sys : LockstepSystem)
    (sm : sys.SM) (ss : sys.SS)
    (a : sys.ActionIdx) (rest : List sys.ActionIdx)
    (ha_opaque : ∀ rs rm, bridge_equiv (sys.bridge a) rs rm)
    (hfail : ¬ runner_passes sys (a :: rest) sm ss) :
    ¬ runner_passes sys rest
        (sys.step_model a sm).1 (sys.step_sut a ss).1 := by
  intro hrest
  apply hfail
  simp only [runner_passes]
  exact ⟨ha_opaque _ _, hrest⟩

/--
  **Opaque step always passes in runner**: an opaque action at the
  head of a trace contributes nothing to the runner check -- it passes
  iff the tail passes on the successor states.
-/
theorem opaque_runner_transparent (sys : LockstepSystem)
    (sm : sys.SM) (ss : sys.SS)
    (a : sys.ActionIdx) (rest : List sys.ActionIdx)
    (ha_opaque : ∀ rs rm, bridge_equiv (sys.bridge a) rs rm) :
    runner_passes sys (a :: rest) sm ss
    ↔ runner_passes sys rest
        (sys.step_model a sm).1 (sys.step_sut a ss).1 := by
  simp only [runner_passes]
  constructor
  · exact fun ⟨_, hrest⟩ => hrest
  · exact fun hrest => ⟨ha_opaque _ _, hrest⟩

-- =========================================================================
-- Depth sensitivity
-- =========================================================================

/--
  **Opaque at depth 1, failure at depth 2**: demonstrates that depth 1
  bisimulation can pass while depth 2 fails. This is the formal
  statement that deeper testing is strictly necessary for systems
  with opaque handles.
-/
theorem opaque_depth_sensitivity (sys : LockstepSystem)
    (sm : sys.SM) (ss : sys.SS)
    -- All actions have opaque bridges (depth 1 always passes)
    (hall_opaque : ∀ (a : sys.ActionIdx) rs rm,
        bridge_equiv (sys.bridge a) rs rm)
    -- But some action b at some successor reveals a difference
    (a b : sys.ActionIdx)
    (hb_fails : ¬ bridge_equiv (sys.bridge b)
        (sys.step_sut b (sys.step_sut a ss).1).2
        (sys.step_model b (sys.step_model a sm).1).2) :
    -- Depth 1 passes...
    bounded_bisim sys 1 sm ss
    -- ...but depth 2 fails
    ∧ ¬ bounded_bisim sys 2 sm ss := by
  constructor
  · -- Depth 1: all bridges are opaque, so bridge_equiv always holds
    simp only [bounded_bisim]
    intro a'
    exact ⟨hall_opaque a' _ _, trivial⟩
  · -- Depth 2: action b fails at successor after a
    exact opaque_step_then_detect sys sm ss a b hb_fails
