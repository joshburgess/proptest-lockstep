/-
  Game-Semantic Characterization of Bisimulation

  Interprets bounded bisimulation as a game between Attacker (who
  tries to distinguish model from SUT) and Defender (who tries to
  show they agree). The Attacker wins by finding an action whose
  bridge check fails; the Defender wins by surviving all rounds.

  The key theorem: `bounded_bisim` at depth n fails iff the Attacker
  has a winning strategy of depth ≤ n. The winning strategy is a
  concrete `BisimWitness` -- a path through the game tree that
  leads to a bridge failure.

  This connects to testing: the witness IS the minimal failing
  test case. The DPOR explorer searches for witnesses; this theorem
  proves the search is complete.
-/

import Metatheory.Lockstep

-- =========================================================================
-- The Attacker's winning strategy
-- =========================================================================

/--
  A **bisimulation witness**: the Attacker's winning strategy in
  the bisimulation game. Each constructor represents a move:

  - `bridge_fail a`: action `a` at the current state has a bridge
    failure -- the Attacker wins immediately.
  - `deeper a w`: action `a` passes its bridge check, but witness
    `w` shows the successor states are distinguishable -- the
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

  This is the constructive direction -- the witness directly
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

  This is the classical direction -- extracting a concrete strategy
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

-- =========================================================================
-- Crash-aware game semantics
-- =========================================================================

/--
  A **crash-aware witness**: the Attacker's strategy in the crash
  bisimulation game. Extends `BisimWitness` with crash moves:

  - `bridge_fail a`: bridge failure at action a (immediate win)
  - `invariant_fail`: the model invariant fails (immediate win)
  - `deeper a w`: action a passes, continue with witness w
  - `crash_then w`: crash (recover), continue with witness w

  The crash move is the key addition: the Attacker can choose to
  crash the system and continue playing from the recovered state.
-/
inductive CrashWitness (A : Type) where
  | bridge_fail : A → CrashWitness A
  | invariant_fail : CrashWitness A
  | deeper : A → CrashWitness A → CrashWitness A
  | crash_then : CrashWitness A → CrashWitness A

/--
  Validity of a crash-aware witness at model/SUT states.
-/
def crash_witness_valid (ls : LockstepSystem)
    (checkpoint : ls.SM → DS) (model_recover : DS → ls.SM)
    (sut_recover : ls.SS → ls.SS) (invariant : ls.SM → Prop) :
    CrashWitness ls.ActionIdx → ls.SM → ls.SS → Prop
  | .bridge_fail a, sm, ss =>
    ¬ bridge_equiv (ls.bridge a) (ls.step_sut a ss).2 (ls.step_model a sm).2
  | .invariant_fail, sm, _ =>
    ¬ invariant sm
  | .deeper a w, sm, ss =>
    bridge_equiv (ls.bridge a) (ls.step_sut a ss).2 (ls.step_model a sm).2
    ∧ crash_witness_valid ls checkpoint model_recover sut_recover invariant w
      (ls.step_model a sm).1 (ls.step_sut a ss).1
  | .crash_then w, sm, ss =>
    crash_witness_valid ls checkpoint model_recover sut_recover invariant w
      (model_recover (checkpoint sm)) (sut_recover ss)

/-- Depth of a crash-aware witness. -/
def CrashWitness.depth : CrashWitness A → Nat
  | .bridge_fail _ => 1
  | .invariant_fail => 1
  | .deeper _ w => 1 + w.depth
  | .crash_then w => 1 + w.depth

-- =========================================================================
-- Witness simplification: crash-transparent elimination
-- =========================================================================

/--
  **CRASH-TRANSPARENT WITNESS SIMPLIFICATION**: if a crash witness
  contains `deeper a (crash_then w)` (action a followed by crash)
  and action a is crash-transparent, the witness can be simplified
  to `crash_then w'` where w' is w with states adjusted.

  This is the game-semantic version of crash_transparent_eliminate:
  the Attacker's strategy `[action a, crash, ...]` is DOMINATED by
  `[crash, ...]` when a is crash-transparent. The Attacker gains
  nothing by playing a before crashing.

  The proof shows: the simplified witness is valid wherever the
  original is valid, with strictly smaller depth. This means the
  crash-interleaving explorer can prune [transparent, crash]
  sequences from its search space without missing any winning
  strategy.
-/
theorem crash_witness_transparent_simplify {DS : Type}
    (ls : LockstepSystem)
    (a : ls.ActionIdx) (w : CrashWitness ls.ActionIdx)
    (sm : ls.SM) (ss : ls.SS)
    (checkpoint : ls.SM → DS) (model_recover : DS → ls.SM)
    (sut_recover : ls.SS → ls.SS) (invariant : ls.SM → Prop)
    (hchk : checkpoint (ls.step_model a sm).1 = checkpoint sm)
    (hsut : sut_recover (ls.step_sut a ss).1 = sut_recover ss)
    -- The [action a, crash, w] witness is valid
    (hvalid : crash_witness_valid ls checkpoint model_recover sut_recover invariant
      (.deeper a (.crash_then w)) sm ss) :
    -- Then the simplified [crash, w] witness is ALSO valid
    crash_witness_valid ls checkpoint model_recover sut_recover invariant
      (.crash_then w) sm ss := by
  -- hvalid.2 : crash_witness_valid ... w
  --   (model_recover (checkpoint (step_model a sm).1))
  --   (sut_recover (step_sut a ss).1)
  -- Goal: crash_witness_valid ... w
  --   (model_recover (checkpoint sm))
  --   (sut_recover ss)
  simp only [crash_witness_valid] at hvalid ⊢
  rw [← hchk, ← hsut]
  exact hvalid.2

/--
  **Simplified witness has smaller depth**: the crash-then witness
  is strictly shallower than the deeper-crash_then witness.
-/
theorem crash_witness_simplify_depth (a : A)
    (w : CrashWitness A) :
    (CrashWitness.crash_then w).depth < (CrashWitness.deeper a (.crash_then w)).depth := by
  simp [CrashWitness.depth]

-- =========================================================================
-- Crash bisimulation game semantic biconditional
-- =========================================================================

/--
  **Parameterized crash bisimulation**: crash_bisim defined with
  LockstepSystem + crash functions as separate parameters,
  avoiding CrashRecoverySystem field projection issues.

  This is definitionally equivalent to `crash_bisim sys n sm ss`
  when given `sys.toLockstepSystem`, `sys.checkpoint`, etc.
-/
def crash_bisim_param {DS : Type} (ls : LockstepSystem)
    (checkpoint : ls.SM → DS) (model_recover : DS → ls.SM)
    (sut_recover : ls.SS → ls.SS) (invariant : ls.SM → Prop) :
    Nat → ls.SM → ls.SS → Prop
  | 0, _, _ => True
  | n + 1, sm, ss =>
    invariant sm
    ∧ (∀ (a : ls.ActionIdx),
        bridge_equiv (ls.bridge a) (ls.step_sut a ss).2 (ls.step_model a sm).2
        ∧ crash_bisim_param ls checkpoint model_recover sut_recover invariant n
          (ls.step_model a sm).1 (ls.step_sut a ss).1)
    ∧ crash_bisim_param ls checkpoint model_recover sut_recover invariant n
        (model_recover (checkpoint sm)) (sut_recover ss)

/--
  **Crash witness soundness** (backward direction, constructive):
  a valid crash witness of depth ≤ n proves ¬crash_bisim_param.
-/
theorem crash_witness_soundness {DS : Type} (ls : LockstepSystem)
    (checkpoint : ls.SM → DS) (model_recover : DS → ls.SM)
    (sut_recover : ls.SS → ls.SS) (invariant : ls.SM → Prop)
    (w : CrashWitness ls.ActionIdx) (n : Nat)
    (sm : ls.SM) (ss : ls.SS)
    (hvalid : crash_witness_valid ls checkpoint model_recover sut_recover invariant w sm ss)
    (hdepth : w.depth ≤ n) :
    ¬ crash_bisim_param ls checkpoint model_recover sut_recover invariant n sm ss := by
  induction w generalizing sm ss n with
  | bridge_fail a =>
    intro h
    match n with
    | 0 => simp [CrashWitness.depth] at hdepth
    | n' + 1 =>
      simp only [crash_bisim_param] at h
      exact hvalid (h.2.1 a).1
  | invariant_fail =>
    intro h
    match n with
    | 0 => simp [CrashWitness.depth] at hdepth
    | n' + 1 =>
      simp only [crash_bisim_param] at h
      exact hvalid h.1
  | deeper a w ih =>
    intro h
    match n with
    | 0 => simp [CrashWitness.depth] at hdepth
    | n' + 1 =>
      simp only [crash_bisim_param] at h
      simp only [crash_witness_valid] at hvalid
      exact ih n' _ _ hvalid.2
        (by simp [CrashWitness.depth] at hdepth; omega) (h.2.1 a).2
  | crash_then w ih =>
    intro h
    match n with
    | 0 => simp [CrashWitness.depth] at hdepth
    | n' + 1 =>
      simp only [crash_bisim_param] at h
      exact ih n' _ _ hvalid
        (by simp [CrashWitness.depth] at hdepth; omega) h.2.2

/--
  **Crash witness completeness** (forward direction, classical):
  if crash_bisim_param fails at depth n, there exists a valid
  crash witness of depth ≤ n.

  This requires classical logic to extract the failing component
  from ¬(invariant ∧ (∀ a, ...) ∧ crash_recurse), and bridge
  decidability to determine whether the failure is at the bridge
  or deeper.

  The proof has FOUR branches (vs two for bisim_game_semantic):
  1. Invariant failure → .invariant_fail
  2. Bridge failure at some action → .bridge_fail a
  3. Bridge passes but successor fails → .deeper a (recursive)
  4. Crash-recovery successor fails → .crash_then (recursive)
-/
theorem crash_witness_completeness {DS : Type} (ls : LockstepSystem)
    (checkpoint : ls.SM → DS) (model_recover : DS → ls.SM)
    (sut_recover : ls.SS → ls.SS) (invariant : ls.SM → Prop)
    (dinv : ∀ s, Decidable (invariant s))
    (n : Nat) (sm : ls.SM) (ss : ls.SS)
    (h : ¬ crash_bisim_param ls checkpoint model_recover sut_recover invariant n sm ss) :
    ∃ (w : CrashWitness ls.ActionIdx),
      crash_witness_valid ls checkpoint model_recover sut_recover invariant w sm ss
      ∧ w.depth ≤ n := by
  induction n generalizing sm ss with
  | zero => exact absurd trivial h
  | succ k ih =>
    -- ¬(invariant ∧ (∀ a, bridge ∧ recurse) ∧ crash_recurse)
    -- Split into four cases
    have : Decidable (invariant sm) := dinv sm
    by_cases hinv : invariant sm
    · -- Invariant holds. Must be action or crash failure.
      by_cases hcrash : crash_bisim_param ls checkpoint model_recover
          sut_recover invariant k (model_recover (checkpoint sm)) (sut_recover ss)
      · -- Crash recurse passes. Must be action failure.
        have haction : ∃ a, ¬ (bridge_equiv (ls.bridge a)
            (ls.step_sut a ss).2 (ls.step_model a sm).2
          ∧ crash_bisim_param ls checkpoint model_recover sut_recover invariant k
            (ls.step_model a sm).1 (ls.step_sut a ss).1) := by
          exact Classical.byContradiction fun hall =>
            h ⟨hinv, fun a => Classical.byContradiction fun ha =>
              hall ⟨a, ha⟩, hcrash⟩
        obtain ⟨a, ha⟩ := haction
        -- Does bridge fail or does successor fail?
        have hdec := bridge_equiv_decidable (ls.bridge a)
            (ls.step_sut a ss).2 (ls.step_model a sm).2
        match hdec with
        | .isFalse hbf =>
          exact ⟨.bridge_fail a, hbf, by simp [CrashWitness.depth]⟩
        | .isTrue hbp =>
          have hsucc : ¬ crash_bisim_param ls checkpoint model_recover
              sut_recover invariant k
              (ls.step_model a sm).1 (ls.step_sut a ss).1 := by
            intro hc; exact ha ⟨hbp, hc⟩
          obtain ⟨w, hv, hd⟩ := ih _ _ hsucc
          exact ⟨.deeper a w, ⟨hbp, hv⟩, by simp [CrashWitness.depth]; omega⟩
      · -- Crash recurse fails → .crash_then
        obtain ⟨w, hv, hd⟩ := ih _ _ hcrash
        exact ⟨.crash_then w, hv, by simp [CrashWitness.depth]; omega⟩
    · -- Invariant fails → immediate witness
      exact ⟨.invariant_fail, hinv, by simp [CrashWitness.depth]⟩

/--
  **THE CRASH BISIMULATION GAME SEMANTIC BICONDITIONAL**:
  crash_bisim_param at depth n fails if and only if the Attacker
  has a valid crash witness of depth ≤ n.

  This extends `bisim_game_semantic` to crash-recovery systems
  with four Attacker moves (action, crash, bridge_fail,
  invariant_fail) and proves the same completeness and soundness
  properties. The witness IS the minimal failing test case
  including crash events.

  Combined with `crash_witness_transparent_simplify`, this proves
  that the crash explorer's search space (after pruning transparent
  actions) is COMPLETE: every crash_bisim failure has a witness,
  and pruning reduces witness depth without losing validity.
-/
theorem crash_bisim_game_semantic {DS : Type} (ls : LockstepSystem)
    (checkpoint : ls.SM → DS) (model_recover : DS → ls.SM)
    (sut_recover : ls.SS → ls.SS) (invariant : ls.SM → Prop)
    (dinv : ∀ s, Decidable (invariant s))
    (n : Nat) (sm : ls.SM) (ss : ls.SS) :
    ¬ crash_bisim_param ls checkpoint model_recover sut_recover invariant n sm ss
    ↔ ∃ (w : CrashWitness ls.ActionIdx),
      crash_witness_valid ls checkpoint model_recover sut_recover invariant w sm ss
      ∧ w.depth ≤ n :=
  ⟨crash_witness_completeness ls checkpoint model_recover sut_recover invariant dinv n sm ss,
   fun ⟨w, hv, hd⟩ => crash_witness_soundness ls checkpoint model_recover
     sut_recover invariant w n sm ss hv hd⟩
