/-
  Game-Semantic Characterization of Bisimulation

  Interprets bounded bisimulation as a game between Attacker (who
  tries to distinguish model from SUT) and Defender (who tries to
  show they agree). The Attacker wins by finding an action whose
  bridge check fails; the Defender wins by surviving all rounds.

  The key theorem: `bounded_bisim` at depth n fails iff the Attacker
  has a winning strategy of depth ≤ n. The winning strategy is a
  concrete `BisimWitness` — a path through the game tree that
  leads to a bridge failure.

  This connects to testing: the witness IS the minimal failing
  test case. The DPOR explorer searches for witnesses; this theorem
  proves the search is complete.
-/

import FormalVerification.Lockstep

-- =========================================================================
-- The Attacker's winning strategy
-- =========================================================================

/--
  A **bisimulation witness**: the Attacker's winning strategy in
  the bisimulation game. Each constructor represents a move:

  - `bridge_fail a`: action `a` at the current state has a bridge
    failure — the Attacker wins immediately.
  - `deeper a w`: action `a` passes its bridge check, but witness
    `w` shows the successor states are distinguishable — the
    Attacker wins by continuing.

  The witness is a path through the game tree, not the full tree.
  It records the SPECIFIC sequence of actions that leads to failure.
-/
inductive BisimWitness (sys : LockstepSystem) where
  | bridge_fail : sys.ActionIdx → BisimWitness sys
  | deeper : sys.ActionIdx → BisimWitness sys → BisimWitness sys

-- =========================================================================
-- Witness validity
-- =========================================================================

/--
  A witness is **valid** at states (sm, ss) if it actually
  demonstrates a bridge failure. `bridge_fail a` requires the
  bridge check to fail; `deeper a w` requires the bridge check
  to PASS (the Defender responds) but `w` to be valid at the
  successor states.
-/
def witness_valid (sys : LockstepSystem) :
    BisimWitness sys → sys.SM → sys.SS → Prop
  | .bridge_fail a, sm, ss =>
    ¬ bridge_equiv (sys.bridge a) (sys.step_sut a ss).2 (sys.step_model a sm).2
  | .deeper a w, sm, ss =>
    bridge_equiv (sys.bridge a) (sys.step_sut a ss).2 (sys.step_model a sm).2
    ∧ witness_valid sys w (sys.step_model a sm).1 (sys.step_sut a ss).1

/--
  The **depth** of a witness: the number of rounds in the game.
  Corresponds to the testing depth needed to find this failure.
-/
def BisimWitness.depth : BisimWitness sys → Nat
  | .bridge_fail _ => 1
  | .deeper _ w => 1 + w.depth

-- =========================================================================
-- Backward direction: witness → ¬bounded_bisim (constructive)
-- =========================================================================

/--
  **Witness soundness**: a valid witness of depth ≤ n proves
  that bounded_bisim fails at depth n.

  This is the constructive direction — the witness directly
  encodes the Attacker's winning strategy. No classical logic
  needed.
-/
theorem witness_implies_not_bisim (sys : LockstepSystem)
    (w : BisimWitness sys) (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (hvalid : witness_valid sys w sm ss)
    (hdepth : w.depth ≤ n) :
    ¬ bounded_bisim sys n sm ss := by
  induction w generalizing sm ss n with
  | bridge_fail a =>
    -- The witness says action a's bridge fails
    intro hbisim
    match n with
    | 0 => simp [BisimWitness.depth] at hdepth
    | n' + 1 =>
      simp only [bounded_bisim] at hbisim
      exact hvalid (hbisim a).1
  | deeper a w ih =>
    -- The witness says a's bridge passes, but w fails at successor
    intro hbisim
    obtain ⟨hbridge, hrest⟩ := hvalid
    match n with
    | 0 => simp [BisimWitness.depth] at hdepth
    | n' + 1 =>
      simp only [bounded_bisim] at hbisim
      have ha := hbisim a
      exact ih n' _ _ hrest (by simp [BisimWitness.depth] at hdepth; omega) ha.2

-- =========================================================================
-- Forward direction: ¬bounded_bisim → witness (classical)
-- =========================================================================

/--
  **Witness completeness**: if bounded_bisim fails at depth n,
  there exists a valid witness of depth ≤ n.

  This is the classical direction — extracting a concrete strategy
  from the negation of a universal quantifier requires excluded
  middle. The witness is the Attacker's optimal play.

  Combined with `witness_implies_not_bisim`, this gives the
  game-semantic characterization:
    ¬bounded_bisim ↔ ∃ valid witness
-/
theorem not_bisim_implies_witness (sys : LockstepSystem)
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (h : ¬ bounded_bisim sys n sm ss) :
    ∃ (w : BisimWitness sys),
      witness_valid sys w sm ss ∧ w.depth ≤ n := by
  induction n generalizing sm ss with
  | zero => exact absurd trivial h
  | succ k ih =>
    -- bounded_bisim at k+1 = ∀ a, bridge ∧ bisim(k)
    -- Its negation: ∃ a, ¬bridge ∨ ¬bisim(k)
    have hfail : ∃ a, ¬ bridge_equiv (sys.bridge a)
        (sys.step_sut a ss).2 (sys.step_model a sm).2
      ∨ ¬ bounded_bisim sys k (sys.step_model a sm).1
        (sys.step_sut a ss).1 := by
      exact Classical.byContradiction fun hall => h (by
        simp only [bounded_bisim]
        intro a
        have hna := fun (h : ¬ bridge_equiv _ _ _ ∨ _) => hall ⟨a, h⟩
        constructor
        · exact Classical.byContradiction fun hb => hna (Or.inl hb)
        · exact Classical.byContradiction fun hk => hna (Or.inr hk))
    obtain ⟨a, ha⟩ := hfail
    -- Decide: does bridge fail at a, or does bisim fail at successor?
    have hdec := bridge_equiv_decidable (sys.bridge a)
        (sys.step_sut a ss).2 (sys.step_model a sm).2
    match hdec with
    | .isFalse hbridge_fail =>
      -- Bridge fails → immediate witness
      exact ⟨.bridge_fail a, hbridge_fail, by simp [BisimWitness.depth]⟩
    | .isTrue hbridge_pass =>
      -- Bridge passes → bisim must fail at successor
      have hbisim_fail : ¬ bounded_bisim sys k
          (sys.step_model a sm).1 (sys.step_sut a ss).1 := by
        cases ha with
        | inl hb => exact absurd hbridge_pass hb
        | inr hk => exact hk
      -- Recurse to find witness at successor
      obtain ⟨w, hvalid, hdepth⟩ := ih _ _ hbisim_fail
      exact ⟨.deeper a w, ⟨hbridge_pass, hvalid⟩,
        by simp [BisimWitness.depth]; omega⟩

-- =========================================================================
-- THE GAME-SEMANTIC BICONDITIONAL
-- =========================================================================

/--
  **THE GAME-SEMANTIC CHARACTERIZATION OF BISIMULATION**:
  `bounded_bisim` at depth n fails if and only if the Attacker
  has a valid winning strategy (witness) of depth ≤ n.

  This theorem connects three views of bisimulation:
  1. **Logical**: bounded_bisim is a recursive predicate (∀ actions, ...)
  2. **Observational**: observational_refinement_equiv (∀ traces, obs equal)
  3. **Game-semantic**: the Attacker has no winning strategy (this theorem)

  The witness IS the minimal failing test case: it records exactly
  which actions to take and where the bridge failure occurs. The
  DPOR explorer's job is to search for witnesses efficiently;
  this theorem proves the search is complete.
-/
theorem bisim_game_semantic (sys : LockstepSystem)
    (n : Nat) (sm : sys.SM) (ss : sys.SS) :
    ¬ bounded_bisim sys n sm ss
    ↔ ∃ (w : BisimWitness sys),
        witness_valid sys w sm ss ∧ w.depth ≤ n :=
  ⟨not_bisim_implies_witness sys n sm ss,
   fun ⟨w, hv, hd⟩ => witness_implies_not_bisim sys w n sm ss hv hd⟩
