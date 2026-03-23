# Three Characterizations of Lockstep Bisimulation: Logical, Observational, and Game-Semantic

## POPL — Draft Outline & Introduction

### The One Idea

Bounded bisimulation for property-based testing admits three equivalent characterizations — as a recursive predicate, as trace-based observational indistinguishability, and as the absence of Attacker winning strategies in a bisimulation game — and all three extend uniformly to crash-recovery systems. We machine-check every equivalence as a biconditional in Lean 4 with zero sorry.

---

## Outline

### 1. Introduction (~2.5 pages)

See full draft below.

### 2. Bounded Bisimulation as a Recursive Predicate (~3 pages)

We define lockstep systems (`LockstepSystem`) parameterized by model and SUT state types, an action index, per-action return types, and a bridge algebra that determines what is observed. Bounded bisimulation (`bounded_bisim n sm ss`) is a recursive predicate: at depth zero it holds trivially; at depth n+1 it requires that for every action, the bridge observations agree and the successor states satisfy the bisimulation at depth n. We prove monotonicity in depth (`bounded_bisim_mono`) and that full coinductive bisimulation (`lockstep_bisim`) is the infinite-depth limit. The bridge algebra — a span through a decidable observation type — is the logical relation that determines observational granularity. We recall the key property that finer bridges give strictly stronger bisimulation guarantees (`refines_strengthen_bisim`).

### 3. The Runner Correspondence (~2.5 pages)

We formalize the test runner's operational semantics as a trace-based predicate (`runner_passes`) and prove the first biconditional: `runner_bounded_bisim_equiv`, stating that the runner passes on all traces of length n if and only if bounded bisimulation holds at depth n. The forward direction (`runner_implies_bounded_bisim`) shows that operational bridge checks at each step establish the declarative bisimulation. The reverse direction (`bounded_bisim_implies_runner`) shows that the bisimulation implies every concrete trace passes. This closes the gap between the Rust implementation (`LockstepSut::apply`) and the mathematical definition.

### 4. Observational Refinement (~3 pages)

We define trace-level observations — the bridge observation produced by the SUT (respectively, the model) after running a prefix of actions — and prove the second biconditional: `observational_refinement_equiv`, stating that bounded bisimulation at depth n holds if and only if for every prefix of length less than n and every action, the SUT and model produce identical bridge observations. The forward direction is the "free theorem": bisimulation implies observational indistinguishability. The reverse direction, which is more subtle, reconstructs the bisimulation from the assumption that all trace-level observations match, by induction on depth. We prove the intermediate lemma `bisim_along_trace` showing bisimulation is preserved along prefixes. Together with the runner correspondence, this yields the full triangle: runner passes iff bounded bisimulation iff observational refinement.

### 5. The Game-Semantic Characterization (~3 pages)

We introduce the Attacker-Defender bisimulation game. The Attacker's winning strategy is a `BisimWitness` — an inductive type with two constructors: `bridge_fail a` (the bridge check fails at action a, giving an immediate win) and `deeper a w` (action a passes its bridge check, but witness w demonstrates failure at the successor states). A witness is valid (`witness_valid`) when the bridge failures and passes it claims are genuine. We prove the third biconditional: `bisim_game_semantic`, stating that bounded bisimulation at depth n fails if and only if there exists a valid `BisimWitness` of depth at most n. The constructive direction (`witness_implies_not_bisim`) requires no classical logic: the witness directly refutes the bisimulation. The classical direction (`not_bisim_implies_witness`) extracts a concrete Attacker strategy from the negation of the universal quantifier, using excluded middle and the decidability of bridge equivalence. The witness IS the minimal failing test case.

### 6. Testing Completeness (~1.5 pages)

We prove `testing_completeness`: any observable discrepancy between SUT and model — a prefix and action at which bridge observations differ — implies that bounded bisimulation fails at the corresponding depth. This is the contrapositive of observational refinement. Combined with the game-semantic characterization, it gives a concrete computational interpretation: every observable bug has a `BisimWitness` that encodes the action sequence exposing it. We also prove `bug_localization`: when bisimulation fails at depth n+1, either a bridge check fails at the current state or the bisimulation fails at depth n at some successor.

### 7. Extension to Crash-Recovery Systems (~4 pages)

We extend all three characterizations to crash-recovery systems (`CrashRecoverySystem`), which add durable state, checkpoint and recovery functions, and a state invariant. Crash bisimulation (`crash_bisim`) strengthens bounded bisimulation with three additional requirements at each depth: the invariant holds, normal actions satisfy bridge equivalence and the bisimulation at the successor, and after a crash the recovered states satisfy the bisimulation. We prove that crash bisimulation strictly implies bounded bisimulation (`crash_bisim_implies_bounded`) and is monotone in depth.

The crash-aware Attacker has four moves, formalized as `CrashWitness`: `bridge_fail a` (bridge failure), `invariant_fail` (invariant violation), `deeper a w` (continue past a passing action), and `crash_then w` (crash the system and continue playing from recovered states). We prove the crash game-semantic biconditional `crash_bisim_game_semantic`: crash bisimulation fails at depth n if and only if a valid `CrashWitness` of depth at most n exists. The completeness direction requires decidability of both bridge equivalence and the state invariant, and branches into four cases corresponding to the four Attacker moves.

### 8. Crash-Transparent Elimination and Strategy Dominance (~3 pages)

We define crash-transparent actions: actions whose effects are erased by a subsequent crash (`checkpoint` is invariant and SUT recovery undoes the action's effects). The key theorem is `crash_witness_transparent_simplify`: if a crash witness contains the subsequence `deeper a (crash_then w)` and action a is crash-transparent, the witness simplifies to `crash_then w` — which is valid wherever the original is valid and has strictly smaller depth (`crash_witness_simplify_depth`). This is strategy dominance: the Attacker gains nothing by playing a crash-transparent action before crashing.

At the trace level, we prove `crash_transparent_eliminate_model`: in a crash-interleaved trace, a crash-transparent action immediately before a crash can be removed without changing the final model state. The multi-pair generalization `reduce_crash_trace_preserves_state` shows that eliminating all such pairs simultaneously preserves the final state. These results justify pruning in crash-interleaving exploration: the search space reduction is exponential in the number of crash-transparent actions, and completeness is preserved.

### 9. The Consistency Hierarchy (~2 pages)

We place bounded bisimulation within a hierarchy of consistency notions — session bisimulation (per-session read-your-writes), convergent bisimulation (eventual consistency after sync), and bounded bisimulation (linearizability) — and prove the hierarchy is strict. Two concrete counterexample systems, constructed in Lean, witness both gaps: `convergent_strictly_weaker` exhibits a system satisfying convergent bisimulation but failing bounded bisimulation (the "stale read" pattern), and `session_strictly_stronger` exhibits a system satisfying convergent bisimulation at every depth but failing session bisimulation at depth 2 (a write-then-read sequence violating read-your-writes). The hierarchy is bounded_bisim strictly implies session_bisim strictly implies convergent_bisim.

### 10. Invariant Bisimulation and Preconditioned Testing (~2 pages)

We define invariant bisimulation (`invariant_bisim`), which augments bounded bisimulation with a state predicate that must hold at every reachable model state. We prove it strictly implies bounded bisimulation and that the invariant propagates along traces (`invariant_along_trace`). Preconditioned bisimulation restricts the Attacker to actions satisfying a precondition at the current state, weakening the universal quantifier. We prove that preconditioned bisimulation is strictly weaker than the unrestricted version and that preconditions compose with invariants.

### 11. Discussion and Related Work (~2 pages)

We compare with process-algebraic bisimulation theory (Milner, Park), where the logical/observational/game-semantic triangle is classical but informal; our contribution is the machine-checked treatment for a testing framework with crash-recovery. We compare with Jepsen (empirical crash testing, no formal guarantees) and Perennial (full crash-recovery verification in Coq, heavyweight); our formalization occupies the intermediate ground of soundly tested crash recovery. We discuss the connection to Reynolds' abstraction theorem (the bridge is a logical relation, observational refinement is the free theorem) and to Abramsky-Jagadeesan-Malacaria game semantics (the witness is a strategy, the biconditional is full abstraction at finite depth). We note limitations: bounded bisimulation covers only finite-depth interaction, the formalization assumes deterministic step functions, and the Lean proofs are not extracted to executable code.

### 12. Conclusion (~0.5 pages)

We summarize the three biconditionals and their crash-recovery extensions as a coherent metatheory for property-based testing. The 182 machine-checked theorems, with zero sorry, make each claim a theorem rather than a belief.

---

## Introduction

Property-based testing of stateful systems rests on a simple operational idea: maintain a model and a system-under-test (SUT) in lockstep, apply the same sequence of actions to both, and check that their outputs agree at each step. This "lockstep" paradigm, originating in de Vries's quickcheck-lockstep for Haskell, underpins the most practical approaches to testing data structures, databases, and concurrent systems. Yet the theoretical status of what a passing lockstep test actually proves has remained informal. Practitioners speak of "the SUT conforming to the model," but the precise semantic content of this claim — and its relationship to classical notions from process algebra, such as bisimulation and observational equivalence — has not been established by machine-checked proof.

We present three equivalent characterizations of bounded bisimulation as it arises in lockstep property-based testing, together with their extensions to crash-recovery systems, all formalized in Lean 4 with zero uses of `sorry`.

**The logical characterization.** Bounded bisimulation at depth n is a recursive predicate: at depth zero it holds vacuously; at depth n+1 it requires that for every action, a bridge relation holds on the outputs and the successor states satisfy the bisimulation at depth n. The bridge is not mere equality — it is a span through a decidable observation type, a binary logical relation in the sense of Reynolds that determines what aspects of the output are observable. This parameterization by bridges is essential: real systems return opaque handles, wrapped errors, and nested structures, and the bridge algebra specifies precisely what the test observes.

**The observational characterization.** Bounded bisimulation at depth n holds if and only if for every prefix of fewer than n actions and every subsequent action, the bridge observation produced by the SUT equals the bridge observation produced by the model. This is the analogue of Reynolds' abstraction theorem: the bridge is a logical relation, and the biconditional (`observational_refinement_equiv`) states that no interaction through the bridge API, within the tested depth, can distinguish the SUT from the model. The forward direction — bisimulation implies indistinguishability — is the "free theorem." The reverse direction — indistinguishability implies bisimulation — reconstructs the recursive predicate from trace-level agreement by induction on depth. A separate correspondence theorem (`runner_bounded_bisim_equiv`) shows that the test runner's operational behavior — checking bridge equivalence at each step of each trace — is equivalent to bounded bisimulation, closing the gap between the implementation and the mathematical definition.

**The game-semantic characterization.** Bounded bisimulation at depth n fails if and only if the Attacker possesses a valid winning strategy of depth at most n in a bisimulation game (`bisim_game_semantic`). We formalize the Attacker's strategy as an inductive type `BisimWitness` with two moves: claim a bridge failure at a specific action (winning immediately), or choose an action whose bridge check passes and continue with a sub-strategy at the successor states. The constructive direction — a valid witness refutes the bisimulation — requires no classical axioms. The classical direction — failure of bisimulation yields a witness — extracts a concrete strategy using excluded middle and the decidability of bridge equivalence. The witness is not merely an existence proof: it records the exact sequence of actions leading to a bridge failure. It is, concretely, the minimal failing test case.

These three biconditionals form a triangle. The runner correspondence connects implementation to the logical predicate. Observational refinement connects the logical predicate to trace-level indistinguishability. The game-semantic characterization connects failure of the predicate to the existence of concrete counterexamples. Each edge is a biconditional, not merely an implication, and each direction carries distinct proof-theoretic content.

We extend all three characterizations to crash-recovery systems — systems equipped with durable state, checkpoint and recovery functions, and a state invariant. Crash bisimulation strengthens bounded bisimulation by additionally requiring that the invariant holds at every reachable state and that after a crash, the recovered model and SUT states satisfy the bisimulation. The crash-aware Attacker has four moves rather than two: bridge failure, invariant violation, continuation past a passing action, and crashing the system to play from recovered states. We prove the crash game-semantic biconditional (`crash_bisim_game_semantic`), which requires decidability of both the bridge equivalence and the state invariant.

A key result for practical crash-recovery testing is crash-transparent elimination. An action is crash-transparent if a subsequent crash erases its effects: the checkpoint is invariant and SUT recovery undoes the action. We prove that in any crash witness, a crash-transparent action immediately preceding a crash can be eliminated, yielding a valid witness of strictly smaller depth (`crash_witness_transparent_simplify`). This is strategy dominance: the Attacker's strategy `[action a, crash, ...]` is dominated by `[crash, ...]` when a is crash-transparent. At the trace level, we prove that eliminating all crash-transparent actions before crash points preserves the final state (`reduce_crash_trace_preserves_state`), justifying exponential pruning of the crash-interleaving search space without sacrificing completeness.

Finally, we place these bisimulation notions within a consistency hierarchy — bounded bisimulation (linearizability), session bisimulation (per-session ordering guarantees such as read-your-writes), and convergent bisimulation (eventual consistency after synchronization) — and prove the hierarchy is strict. Two concrete Lean counterexamples witness the gaps: a stale-read system that is eventually consistent but not linearizable, and a read-your-writes violation that is eventually consistent at every depth but fails session bisimulation at depth two.

The formalization comprises 20 Lean 4 files containing 182 machine-checked theorems with zero `sorry`. Every theorem statement in this paper corresponds to a named definition in the Lean development that typechecks against Lean's kernel. The Lean source is available as supplementary material.

---

## 2. Bounded Bisimulation as a Recursive Predicate

We begin by defining the formal framework in which all three characterizations live. A *lockstep system* is a tuple `(SM, SS, ActionIdx, RetM, RetS, bridge, step_model, step_sut)` where `SM` and `SS` are the model and SUT state types, `ActionIdx` indexes the set of actions, `RetM` and `RetS` assign per-action return types, `bridge` assigns a bridge to each action, and `step_model` and `step_sut` are the deterministic transition functions. In Lean 4:

```
structure LockstepSystem where
  SM : Type
  SS : Type
  ActionIdx : Type
  RetM : ActionIdx -> Type
  RetS : ActionIdx -> Type
  bridge : (a : ActionIdx) -> Bridge (RetS a) (RetM a)
  step_model : (a : ActionIdx) -> SM -> SM x RetM a
  step_sut : (a : ActionIdx) -> SS -> SS x RetS a
```

The central abstraction is the *bridge*. A bridge between types `R` and `M` is a span through a decidable observation type:

```
structure Bridge (R : Type) (M : Type) where
  Observed : Type
  observe_real : R -> Observed
  observe_model : M -> Observed
  dec_eq : DecidableEq Observed
```

Two values are *bridge-equivalent* when their observations coincide: `bridge_equiv b r m := b.observe_real r = b.observe_model m`. The decidability of `Observed` ensures that bridge equivalence is a decidable proposition, which is essential for both the computational content of the test runner and the classical direction of the game-semantic characterization.

The bridge is a logical relation in the sense of Reynolds [42]. The `transparent` bridge sets `Observed = T` with identity observation functions, yielding exact equality. The `opaque` bridge sets `Observed = Unit`, yielding the trivial relation that holds for all pairs. Between these extremes, the bridge algebra provides sum lifts (`sumBridge`), product lifts (`prodBridge`), option lifts (`optionBridge`), and list lifts (`listBridge`), each preserving equivalence structurally. These lifts are monotone with respect to a refinement preorder: `bridge_refines b1 b2` holds when every pair related by `b1` is also related by `b2`. We prove reflexivity (`refines_refl`), transitivity (`refines_trans`), that opaque is the coarsest bridge (`opaque_coarsest`), and that transparent is the finest among uniform-observation bridges (`transparent_refines_uniform`).

**Definition 2.1** (Bounded bisimulation). *Let `sys` be a lockstep system. The bounded bisimulation relation `bounded_bisim sys n sm ss` is defined by recursion on `n`:*

- *`bounded_bisim sys 0 sm ss := True`*
- *`bounded_bisim sys (n+1) sm ss := forall a, let (sm', rm) := step_model a sm; let (ss', rs) := step_sut a ss; bridge_equiv (bridge a) rs rm /\ bounded_bisim sys n sm' ss'`*

At depth zero, the relation holds vacuously. At depth `n+1`, for every action `a`, the bridge observation must agree on the outputs and the successor states must satisfy the bisimulation at depth `n`. The universal quantification over actions makes this a *simulation* condition: the SUT must match the model on every possible input, not merely on a specific trace.

Full (coinductive) bisimulation is the infinite-depth limit:

**Definition 2.2** (Full bisimulation). *`lockstep_bisim sys sm ss := forall n, bounded_bisim sys n sm ss`.*

We establish the following foundational properties:

**Theorem 2.3** (Monotonicity). *For all `n <= m`, `bounded_bisim sys m sm ss` implies `bounded_bisim sys n sm ss`.*

*Proof sketch.* By induction on `n`. The base case is trivial. In the inductive case, `bounded_bisim sys (k+1) sm ss` requires `bounded_bisim sys k sm' ss'` at successors, and the inductive hypothesis gives `bounded_bisim sys k sm' ss'` from `bounded_bisim sys m' sm' ss'` when `k <= m'`. The arithmetic follows from `k+1 <= m'+1`. QED.

**Theorem 2.4** (Single-step agreement). *If for every action `a`, the bridge check passes at states `(sm, ss)`, then `bounded_bisim sys 1 sm ss` holds.*

This follows immediately from the definition, since the successor bisimulation at depth zero is trivially true.

**Theorem 2.5** (Bridge refinement strengthens bisimulation). *Let `bridge2` be a family of bridges such that `bridge_refines (sys.bridge a) (bridge2 a)` for all `a`. Then `bounded_bisim sys n sm ss` implies `bounded_bisim {sys with bridge := bridge2} n sm ss`.*

*Proof sketch.* By induction on `n`. The bridge check at each step is transferred via the refinement hypothesis, and the successor bisimulation is identical because step functions are unchanged. QED.

This theorem is the formal expression of a key design principle: finer bridges give strictly stronger guarantees. Replacing an opaque bridge with a transparent one increases the discriminating power of the bisimulation without changing the system's dynamics.

---

## 3. The Runner Correspondence

The test runner's operational behavior is a trace-based predicate. A trace is a list of action indices. The runner processes a trace left to right, at each step running both the model and SUT transition functions, checking bridge equivalence on the outputs, and continuing with the successor states:

**Definition 3.1** (Runner). *`runner_passes sys trace sm ss` is defined by recursion on `trace`:*

- *`runner_passes sys [] sm ss := True`*
- *`runner_passes sys (a :: rest) sm ss := let (sm', rm) := step_model a sm; let (ss', rs) := step_sut a ss; bridge_equiv (bridge a) rs rm /\ runner_passes sys rest sm' ss'`*

This definition mirrors the Rust implementation `LockstepSut::apply`, which processes a sequence of actions: for each action, it runs `step_model`, runs `step_sut`, checks `bridge_equiv` on the results, and continues with the successor states.

The runner correspondence theorem establishes that the runner's operational checks are equivalent to the declarative bisimulation:

**Theorem 3.2** (Runner Correspondence, `runner_bounded_bisim_equiv`). *For all lockstep systems `sys`, natural numbers `n`, and initial states `sm`, `ss`:*

*(forall trace, |trace| = n -> runner_passes sys trace sm ss) <-> bounded_bisim sys n sm ss*

*Proof of the forward direction (`runner_implies_bounded_bisim`).* By induction on `n`. The base case is trivial. For the inductive case, we must show that `bounded_bisim sys (k+1) sm ss` holds, given that the runner passes on all traces of length `k+1`. Fix an action `a`. The runner passes on all traces of the form `a :: rest` where `|rest| = k`. In particular, it passes on the trace `a :: replicate k a`, which gives us the bridge check for `a` at `(sm, ss)`. For the successor bisimulation at depth `k`, we apply the inductive hypothesis to all traces of length `k` starting from `(sm', ss')`, which are precisely the tails of traces starting with `a`. QED.

*Proof of the reverse direction (`bounded_bisim_implies_runner`).* By induction on the trace. The empty trace is immediate. For `a :: rest`, the bisimulation at depth `|a :: rest|` gives the bridge check for `a` and the bisimulation at depth `|rest|` at the successors. The inductive hypothesis yields `runner_passes sys rest sm' ss'`. QED.

The forward direction is the substantive result: it closes the formalization gap between the Rust implementation and the mathematical definition. The runner performs only local, step-by-step bridge checks, yet these local checks collectively establish the global recursive predicate. The reverse direction is the expected soundness: if the bisimulation holds, then every concrete execution passes its bridge checks.

---

## 4. Observational Refinement

We now give the second characterization of bounded bisimulation: as trace-level observational indistinguishability. We define the observations produced by the model and SUT after running a prefix of actions:

**Definition 4.1** (Observations). *The model observation at action `a` in state `sm` is `model_observation sys a sm := (bridge a).observe_model (step_model a sm).2`. The SUT observation is `sut_observation sys a ss := (bridge a).observe_real (step_sut a ss).2`.*

**Definition 4.2** (State after prefix). *`model_state_after sys trace sm` and `sut_state_after sys trace ss` are defined by folding the respective step functions along the trace.*

The single-step result is immediate:

**Theorem 4.3** (Single-step observational refinement, `bisim_implies_equal_observation`). *If `bounded_bisim sys (n+1) sm ss`, then for every action `a`, `sut_observation sys a ss = model_observation sys a sm`.*

The trace-level result requires a lemma showing that bisimulation is preserved along prefixes:

**Theorem 4.4** (Bisimulation along trace, `bisim_along_trace`). *If `bounded_bisim sys (|trace| + n) sm ss`, then `bounded_bisim sys n (model_state_after sys trace sm) (sut_state_after sys trace ss)`.*

*Proof.* By induction on `trace`. The base case is immediate (modulo arithmetic). For `a :: rest`, the bisimulation at depth `|rest| + n + 1` gives the bridge check for `a` and the bisimulation at depth `|rest| + n` at the successors. The inductive hypothesis applies. QED.

With this lemma, the forward direction of observational refinement follows:

**Theorem 4.5** (Observational refinement, `observational_refinement`). *If `bounded_bisim sys n sm ss`, then for every prefix `pre` and action `a` with `|pre| + 1 <= n`, we have `sut_observation sys a (sut_state_after sys pre ss) = model_observation sys a (model_state_after sys pre sm)`.*

*Proof.* Apply `bisim_along_trace` to obtain bisimulation at depth `n - |pre|` at the post-prefix states, then monotonicity to get depth `1`, then the single-step result. QED.

This is the analogue of Reynolds' abstraction theorem: the bridge is a logical relation, and bounded bisimulation is the condition guaranteeing that no interaction through the bridge API, within the tested depth, can distinguish the SUT from the model. The forward direction is the "free theorem."

The reverse direction reconstructs the bisimulation from trace-level observations:

**Theorem 4.6** (Observational refinement biconditional, `observational_refinement_equiv`). *`bounded_bisim sys n sm ss` if and only if for all prefixes `pre` and actions `a` with `|pre| + 1 <= n`, `sut_observation sys a (sut_state_after sys pre ss) = model_observation sys a (model_state_after sys pre sm)`.*

*Proof of the reverse direction.* By induction on `n`. The base case is trivial. For the inductive case, we must establish `bounded_bisim sys (k+1) sm ss`. Fix an action `a`. The bridge check at the current state follows from the hypothesis with `pre = []`, `a = a`, and `|[]| + 1 = 1 <= k + 1`. For the successor bisimulation at depth `k`, we apply the inductive hypothesis with the observation hypothesis shifted: for any prefix `pre'` and action `a'` with `|pre'| + 1 <= k`, we use the original hypothesis with prefix `a :: pre'` and action `a'`, noting that `|a :: pre'| + 1 = |pre'| + 2 <= k + 1`. QED.

Together with the runner correspondence, these three biconditionals form a triangle:

- **Runner <-> Bisimulation** (Theorem 3.2): implementation <-> recursive predicate
- **Bisimulation <-> Observational refinement** (Theorem 4.6): recursive predicate <-> trace-level indistinguishability
- **Runner <-> Observational refinement** (transitive composition): implementation <-> indistinguishability

Each edge is a biconditional, not merely an implication, and each direction carries distinct proof-theoretic content. The forward directions are soundness results (the system satisfies a guarantee); the reverse directions are completeness results (the guarantee implies the system property).

---

## 5. The Game-Semantic Characterization

We now give the third characterization: the failure of bounded bisimulation is equivalent to the existence of an Attacker winning strategy in a bisimulation game. The Attacker's strategy is formalized as an inductive type:

**Definition 5.1** (Bisimulation witness, `BisimWitness`).

```
inductive BisimWitness (sys : LockstepSystem) where
  | bridge_fail : sys.ActionIdx -> BisimWitness sys
  | deeper : sys.ActionIdx -> BisimWitness sys -> BisimWitness sys
```

*The constructor `bridge_fail a` claims that action `a` at the current state has a bridge failure, winning immediately. The constructor `deeper a w` claims that action `a` passes its bridge check, but witness `w` demonstrates failure at the successor states.*

A witness is a path through the game tree, not the full tree. It records the specific sequence of actions that leads to a bridge failure. The depth of a witness counts the number of rounds: `depth (bridge_fail a) = 1` and `depth (deeper a w) = 1 + depth w`.

**Definition 5.2** (Witness validity, `witness_valid`). *A witness is valid at states `(sm, ss)` if the claims it makes are genuine:*

- *`witness_valid sys (bridge_fail a) sm ss := not (bridge_equiv (bridge a) (step_sut a ss).2 (step_model a sm).2)`*
- *`witness_valid sys (deeper a w) sm ss := bridge_equiv (bridge a) (step_sut a ss).2 (step_model a sm).2 /\ witness_valid sys w (step_model a sm).1 (step_sut a ss).1`*

For `bridge_fail a`, validity requires the bridge check to actually fail. For `deeper a w`, validity requires the bridge check to actually pass (the Defender responds), but the sub-witness `w` to be valid at the successor states. This structure ensures that the witness encodes a genuine game play, not merely an arbitrary tree.

**Theorem 5.3** (Witness soundness, `witness_implies_not_bisim`). *If `witness_valid sys w sm ss` and `depth w <= n`, then `not (bounded_bisim sys n sm ss)`.*

*Proof.* By induction on `w`. For `bridge_fail a`, suppose for contradiction that `bounded_bisim sys n sm ss` holds. Since `depth = 1 <= n`, we have `n >= 1`, so write `n = n' + 1`. The bisimulation at depth `n' + 1` gives `bridge_equiv` for action `a`, contradicting the validity of `bridge_fail a`. For `deeper a w`, suppose the bisimulation holds at depth `n = n' + 1`. The bisimulation gives `bridge_equiv` for `a` (consistent with validity) and `bounded_bisim sys n' sm' ss'` at successors. By the inductive hypothesis with the sub-witness `w`, `depth w <= n'`, and `witness_valid sys w sm' ss'`, we obtain a contradiction. QED.

This direction is constructive: the witness directly refutes the bisimulation. No classical logic is required.

**Theorem 5.4** (Witness completeness, `not_bisim_implies_witness`). *If `not (bounded_bisim sys n sm ss)`, then there exists a witness `w` with `witness_valid sys w sm ss` and `depth w <= n`.*

*Proof.* By induction on `n`. The base case `n = 0` is vacuously true (the bisimulation at depth zero holds trivially, contradicting the hypothesis). For `n = k + 1`, the negation of the universal quantifier yields an action `a` at which either the bridge fails or the successor bisimulation fails (by classical logic). The decidability of bridge equivalence (`bridge_equiv_decidable`) then determines which case applies. If the bridge fails, we return `bridge_fail a`. If the bridge passes but the successor bisimulation fails, the inductive hypothesis yields a sub-witness `w` at the successors, and we return `deeper a w`. QED.

This direction is inherently classical: extracting a specific action from `not (forall a, ...)` requires excluded middle. The decidability of bridge equivalence, which every bridge carries via `DecidableEq Observed`, is essential for branching on whether the failure is at the bridge or deeper.

**Theorem 5.5** (Game-semantic biconditional, `bisim_game_semantic`). *`not (bounded_bisim sys n sm ss)` if and only if there exists `w : BisimWitness sys` with `witness_valid sys w sm ss` and `depth w <= n`.*

This theorem connects the logical and game-semantic views: the bisimulation fails precisely when the Attacker possesses a valid winning strategy. The witness is not merely an existence proof; it is a concrete, inspectable object that records the exact sequence of actions leading to a bridge failure. In the implementation, the witness is the minimal failing test case. The DPOR explorer's job is to search for witnesses efficiently; this theorem proves the search is complete.

The connection to Abramsky-Jagadeesan-Malacaria game semantics [1] is direct but specialized. In the general theory, strategies are trees; here, the deterministic step functions reduce strategies to paths. The biconditional is a form of full abstraction at finite depth: every semantic distinction (failure of bisimulation) has a syntactic witness (a strategy), and conversely.

---

## 6. Testing Completeness

The three biconditionals of Sections 3-5 yield a testing completeness result as an immediate corollary. Testing completeness states that any observable discrepancy between the SUT and model is detected by bounded bisimulation at sufficient depth.

**Theorem 6.1** (Testing completeness, `testing_completeness`). *If `sut_observation sys a (sut_state_after sys pre ss) != model_observation sys a (model_state_after sys pre sm)`, then `not (bounded_bisim sys (|pre| + 1) sm ss)`.*

*Proof.* This is the contrapositive of observational refinement (Theorem 4.5). If bounded bisimulation held at depth `|pre| + 1`, then by Theorem 4.5, the observations would agree. QED.

This theorem guarantees the absence of false negatives: if a bug is observable through the bridge algebra within `n` steps, lockstep testing at depth `n` will detect it. The only source of missed bugs is insufficient depth or an overly coarse bridge (one that equates outputs that should be distinguished).

Combined with the game-semantic characterization, testing completeness acquires a computational interpretation:

**Corollary 6.2.** *Every observable bug has a `BisimWitness` that encodes the action sequence exposing it. Specifically, if the SUT and model disagree at prefix `pre` and action `a`, then there exists a valid witness of depth at most `|pre| + 1`.*

*Proof.* By Theorem 6.1, `bounded_bisim` fails at depth `|pre| + 1`. By Theorem 5.5, a valid witness exists. QED.

We also establish a localization result:

**Theorem 6.3** (Bug localization, `bug_localization`). *If `not (bounded_bisim sys (n+1) sm ss)`, then there exists an action `a` such that either (i) the bridge check fails at `a` in the current state, or (ii) `bounded_bisim sys n` fails at the successor states after `a`.*

*Proof.* By classical logic, the negation of `forall a, bridge_equiv ... /\ bounded_bisim ...` yields `exists a, not bridge_equiv ... \/ not bounded_bisim ...`. QED.

Bug localization enables a recursive strategy for identifying the root cause of a bisimulation failure: at each depth, either the current state exhibits a bridge failure (which is directly observable and reportable), or the failure lies deeper, at a specific successor. By iterating, one obtains the full action sequence leading to the failure, which is precisely the witness of Definition 5.1.

---

## 7. Extension to Crash-Recovery Systems

We extend all three characterizations to crash-recovery systems. A *crash-recovery system* augments a lockstep system with durable state, checkpoint and recovery functions, and a state invariant:

**Definition 7.1** (Crash-recovery system, `CrashRecoverySystem`).

```
structure CrashRecoverySystem extends LockstepSystem where
  DS : Type
  checkpoint : SM -> DS
  model_recover : DS -> SM
  sut_recover : SS -> SS
  invariant : SM -> Prop
```

The durable state type `DS` represents what survives a crash. The `checkpoint` function extracts durable state from the model; `model_recover` reconstructs a model state from a checkpoint; `sut_recover` is the SUT's own recovery procedure (which must recover from its own persisted state, without access to the model's checkpoint). The invariant is a predicate that must hold at every reachable model state.

**Definition 7.2** (Crash bisimulation, `crash_bisim`). *Crash bisimulation at depth `n` is defined by:*

- *`crash_bisim sys 0 sm ss := True`*
- *`crash_bisim sys (n+1) sm ss := invariant sm /\ (forall a, bridge_equiv ... /\ crash_bisim sys n sm' ss') /\ crash_bisim sys n (model_recover (checkpoint sm)) (sut_recover ss)`*

At depth `n + 1`, three conditions must hold simultaneously: (1) the state invariant holds at the current model state; (2) for every action, the bridge check passes and the successors satisfy crash bisimulation at depth `n`; and (3) after a crash, the recovered model and SUT states satisfy crash bisimulation at depth `n`. The crash transition consumes one depth unit: recovering and continuing for `n` more steps requires depth `n + 1`.

**Theorem 7.3** (Crash implies bounded, `crash_bisim_implies_bounded`). *`crash_bisim sys n sm ss` implies `bounded_bisim sys.toLockstepSystem n sm ss`.*

*Proof.* By induction on `n`. The crash bisimulation's action clause is strictly stronger than bounded bisimulation's, and the additional invariant and crash clauses are simply dropped. QED.

This implication is strict: crash bisimulation demands that the system not only works correctly under normal execution but also survives crashes with consistent recovery. The converse does not hold in general, as bounded bisimulation makes no claims about crash behavior.

**Theorem 7.4** (Crash monotonicity, `crash_bisim_mono`). *Crash bisimulation is monotone in depth.*

**Theorem 7.5** (Recovery preserves bisimulation, `crash_recovery_preserves`). *If `crash_bisim sys (n+1) sm ss`, then `crash_bisim sys n (model_recover (checkpoint sm)) (sut_recover ss)`.*

**Theorem 7.6** (Double crash, `crash_bisim_double_crash`). *If `crash_bisim sys (n+2) sm ss`, the system survives two consecutive crashes: the doubly-recovered states satisfy crash bisimulation at depth `n`.*

These results justify the crash-recovery testing strategy: if the initial states satisfy crash bisimulation at sufficient depth, then any interleaving of normal actions and crash events produces states that remain in the bisimulation. The test runner explores crash interleavings, confident that the bisimulation is closed under crash-recovery transitions.

### Crash-Aware Game Semantics

The crash-aware Attacker has four moves, formalized as `CrashWitness`:

**Definition 7.7** (Crash witness, `CrashWitness`).

```
inductive CrashWitness (A : Type) where
  | bridge_fail : A -> CrashWitness A
  | invariant_fail : CrashWitness A
  | deeper : A -> CrashWitness A -> CrashWitness A
  | crash_then : CrashWitness A -> CrashWitness A
```

The new moves are `invariant_fail` (claiming the invariant is violated, winning immediately) and `crash_then w` (crashing the system and continuing to play from the recovered states with sub-witness `w`).

Validity (`crash_witness_valid`) and depth (`CrashWitness.depth`) extend straightforwardly:

- `crash_witness_valid ... (invariant_fail) sm ss := not (invariant sm)`
- `crash_witness_valid ... (crash_then w) sm ss := crash_witness_valid ... w (model_recover (checkpoint sm)) (sut_recover ss)`
- `depth (invariant_fail) = 1`; `depth (crash_then w) = 1 + depth w`

**Theorem 7.8** (Crash witness soundness, `crash_witness_soundness`). *A valid crash witness of depth at most `n` proves that crash bisimulation fails at depth `n`. (Constructive.)*

*Proof.* By induction on `w`, following four cases corresponding to the four constructors. Each case extracts the relevant clause from the crash bisimulation definition and derives a contradiction. QED.

**Theorem 7.9** (Crash witness completeness, `crash_witness_completeness`). *If crash bisimulation fails at depth `n`, a valid crash witness of depth at most `n` exists. (Classical; requires decidability of both bridge equivalence and the state invariant.)*

*Proof.* By induction on `n`. For `n = k + 1`, the failure of `invariant sm /\ (forall a, ...) /\ crash_recurse` yields one of four cases: (1) invariant failure, producing `invariant_fail`; (2) bridge failure at some action, producing `bridge_fail a`; (3) bridge passes but successor bisimulation fails, producing `deeper a w` by induction; (4) crash-recovery bisimulation fails, producing `crash_then w` by induction. The branching between cases (2) and (3) uses bridge decidability; the initial branching on the invariant uses its decidability. QED.

**Theorem 7.10** (Crash game-semantic biconditional, `crash_bisim_game_semantic`). *`not (crash_bisim_param ... n sm ss)` if and only if there exists a valid `CrashWitness` of depth at most `n`. Requires decidability of both bridge equivalence and the state invariant.*

---

## 8. Crash-Transparent Elimination and Strategy Dominance

A central result for practical crash-recovery testing is the elimination of crash-transparent actions from Attacker strategies. An action is *crash-transparent* at a given state if a subsequent crash erases its effects:

**Definition 8.1** (Crash-transparent action, `crash_transparent`). *Action `a` is crash-transparent at states `(sm, ss)` if `checkpoint (step_model a sm).1 = checkpoint sm` and `sut_recover (step_sut a ss).1 = sut_recover ss`.*

Intuitively, a crash-transparent action does not modify the durable state: executing it and then crashing produces the same recovered state as crashing without executing it. Typical examples include read-only actions, in-memory logging operations, and any action whose effects are purely volatile.

**Theorem 8.2** (Crash witness simplification, `crash_witness_transparent_simplify`). *If `crash_witness_valid ... (deeper a (crash_then w)) sm ss` holds and action `a` is crash-transparent at `(sm, ss)`, then `crash_witness_valid ... (crash_then w) sm ss` holds.*

*Proof.* The validity of `deeper a (crash_then w)` gives the bridge check for `a` and the validity of `crash_then w` at the successor states `(step_model a sm).1, (step_sut a ss).1`. The validity of `crash_then w` at these successors means `crash_witness_valid ... w (model_recover (checkpoint (step_model a sm).1)) (sut_recover (step_sut a ss).1)`. By crash transparency, `checkpoint (step_model a sm).1 = checkpoint sm` and `sut_recover (step_sut a ss).1 = sut_recover ss`. Rewriting yields `crash_witness_valid ... w (model_recover (checkpoint sm)) (sut_recover ss)`, which is precisely `crash_witness_valid ... (crash_then w) sm ss`. QED.

**Theorem 8.3** (Depth reduction, `crash_witness_simplify_depth`). *`depth (crash_then w) < depth (deeper a (crash_then w))`.*

Together, Theorems 8.2 and 8.3 establish *strategy dominance*: the Attacker's strategy `[action a, crash, ...]` is dominated by `[crash, ...]` when `a` is crash-transparent. The simplified strategy is valid wherever the original is valid, has strictly smaller depth, and reaches the same game-theoretic outcome. The Attacker gains nothing by playing a crash-transparent action before crashing.

### Trace-Level Elimination

At the trace level, we work with crash-interleaved traces, modeled as lists of `CrashEvent` (either `.action a` or `.crash`). The function `crash_model_after` folds such a trace over the model state, applying actions or crash-recovery as appropriate.

**Theorem 8.4** (Single-pair elimination, `crash_transparent_eliminate_model`). *If action `a` is crash-transparent at the model state after prefix `pre`, then `crash_model_after sys (pre ++ [action a, crash] ++ suf) sm = crash_model_after sys (pre ++ [crash] ++ suf) sm`.*

*Proof.* Split the trace at the elimination point using `crash_model_after_append`, then apply the checkpoint transparency condition to show the intermediate states are equal. QED.

**Theorem 8.5** (Multi-pair elimination, `reduce_crash_trace_preserves_state`). *The function `reduce_crash_trace`, which scans a crash-interleaved trace left to right and eliminates every crash-transparent action immediately before a crash event, preserves the final model state.*

*Proof.* By structural induction on the trace, following the recursion pattern of `reduce_crash_trace`. At each `[action a, crash]` pair where `a` is transparent, the checkpoint transparency condition ensures the eliminated and non-eliminated traces produce the same recovered state. QED.

The practical consequence is an exponential reduction in the crash-interleaving search space. If a trace of length `k` has `t` crash-transparent actions, the number of crash interleavings involving these actions is exponential in `t`. Theorem 8.5 shows that all interleavings differing only by the placement of crash-transparent actions before crash points produce the same final state. The test explorer can prune these redundant interleavings while preserving completeness: by Theorem 7.10, every crash bisimulation failure has a crash witness, and by Theorem 8.2, every such witness can be simplified to one that never plays crash-transparent actions before crashes.

### Crash Deferral

A related result concerns the interaction of commutativity and crash points. We define *checkpoint transparency* for a pair of actions:

**Definition 8.6** (Checkpoint transparency for pairs, `checkpoint_transparent`). *Actions `a` and `b` are checkpoint-transparent at model state `sm` if `checkpoint (step_model b (step_model a sm).1).1 = checkpoint (step_model a (step_model b sm).1).1`.*

**Theorem 8.7** (Checkpoint transparency from commutativity, `checkpoint_of_commute`). *If the model states commute under `a` and `b` at `sm`, then checkpoint transparency holds.*

**Theorem 8.8** (Crash deferral, `crash_deferral`). *If `crash_bisim sys (n+3) sm ss` holds, then after executing actions `a` and `b`, the crash-recovered states satisfy `crash_bisim sys n`.*

**Theorem 8.9** (Crash-action swap, `crash_action_swap_model`). *If `checkpoint (step_model a sm).1 = checkpoint sm`, then `model_recover (checkpoint (step_model a sm).1) = model_recover (checkpoint sm)`.*

These results justify a further optimization: when testing crash interleavings, the explorer need not insert crash points between operations that commute at the checkpoint level. The crash point can be deferred past commuting operations without changing the recovered state, eliminating another exponential factor from the search space.

---

## 9. The Consistency Hierarchy

We place bounded bisimulation within a hierarchy of consistency notions and prove the hierarchy is strict. Three levels of consistency are formalized:

**Definition 9.1** (Convergent bisimulation, `convergent_bisim`). *Convergent bisimulation weakens bounded bisimulation by dropping per-step bridge checks. Instead, it requires: (1) the invariant holds, (2) at any point, syncing the model and SUT produces the same observable state (`model_sync sm = sut_sync ss`), and (3) after any action, convergent bisimulation holds at depth `n` on the successors.*

**Definition 9.2** (Session bisimulation, `session_bisim`). *Session bisimulation augments the system with per-session histories that track writes. At each step, it requires that for every read action in a session, the read-your-writes (RYW) guarantee holds: if the session previously wrote value `v` at key `k`, a subsequent read of `k` returns `v`.*

The hierarchy is:

**bounded_bisim (linearizability) => session_bisim (session guarantees) => convergent_bisim (eventual consistency)**

where each arrow denotes "strictly implies." The forward implications follow from the definitions: bounded bisimulation implies session bisimulation (under a bridge-to-RYW compatibility condition, Theorem `bounded_implies_session`), and session bisimulation's successor structure entails convergent bisimulation's requirements.

The reverse implications fail, which we prove by constructing concrete counterexamples:

**Theorem 9.3** (Convergent does not imply bounded, `convergent_strictly_weaker`). *There exists a system such that `convergent_bisim sys 1 () ()` holds but `bounded_bisim sys.toLockstepSystem 1 () ()` fails.*

*Construction.* The `stale_read_system` has a single action that returns `true` from the model and `false` from the SUT, with a transparent bridge. The bridge check fails (`false != true`), so bounded bisimulation fails at depth 1. However, both `model_sync` and `sut_sync` return `()`, so convergent bisimulation holds trivially. This is the "stale read" pattern: the SUT returns stale data, but after synchronization, everything agrees. QED.

**Theorem 9.4** (Session strictly stronger than convergent, `session_strictly_stronger`). *There exists a system such that `convergent_bisim` holds at every depth but `session_bisim` fails at depth 2.*

*Construction.* The `ryw_violation_session` system has two actions: `write` (sets state to `true`, returns `true`) and `read` (returns current model state from the model, but always returns `false` from the SUT). The sync functions are trivial, so convergent bisimulation holds at every depth (`ryw_violation_convergent`). However, the action sequence `[write, read]` violates read-your-writes: the write records `true` in the session history, but the subsequent read observes `false` from the SUT. The RYW check requires `false = true`, a contradiction. Thus `session_bisim` fails at depth 2 (`ryw_violation_not_session`). QED.

These two counterexamples witness both gaps in the three-level hierarchy, making the hierarchy diagram a theorem rather than a claim. The strictness results have practical significance: they show that the choice of consistency level matters. Testing only eventual consistency (convergent bisimulation) may miss linearizability violations, and testing only convergent bisimulation may miss session-level violations such as read-your-writes failures.

---

## 10. Invariant Bisimulation and Preconditioned Testing

We define two refinements of bounded bisimulation that model common testing practices: invariant checking and precondition filtering.

### Invariant Bisimulation

**Definition 10.1** (Invariant system, `InvariantSystem`). *An invariant system extends a lockstep system with a predicate `invariant : SM -> Prop`.*

**Definition 10.2** (Invariant bisimulation, `invariant_bisim`). *Invariant bisimulation at depth `n+1` requires `invariant sm /\ forall a, bridge_equiv ... /\ invariant_bisim sys n sm' ss'`.*

This strengthens bounded bisimulation by additionally requiring the invariant to hold at every reachable model state.

**Theorem 10.3** (`invariant_bisim_implies_bounded`). *Invariant bisimulation implies bounded bisimulation.*

*Proof.* By induction on `n`, dropping the invariant clause at each step. QED.

**Theorem 10.4** (Invariant along trace, `invariant_along_trace`). *If `invariant_bisim sys (|trace| + 1) sm ss`, then `invariant sm`.*

This theorem ensures that the invariant propagates along execution traces. Extensions such as crash-recovery bisimulation (Section 7) build on this property: the crash bisimulation definition includes an invariant clause precisely because crash recovery needs the invariant to hold at every pre-crash state.

**Theorem 10.5** (Invariant at successor, `invariant_bisim_holds_step`). *If `invariant_bisim sys (n+2) sm ss`, the invariant holds at the successor state after any action.*

**Theorem 10.6** (Monotonicity, `invariant_bisim_mono`). *Invariant bisimulation is monotone in depth.*

### Preconditioned Bisimulation

In practice, not all actions are valid at every state. The test runner filters actions through a precondition before executing them:

**Definition 10.7** (Preconditioned system, `PreconditionedSystem`). *A preconditioned system extends a lockstep system with `precond : ActionIdx -> SM -> Prop`.*

**Definition 10.8** (Preconditioned bisimulation, `precond_bisim`). *At depth `n+1`, only actions satisfying `precond a sm` are checked: `forall a, precond a sm -> bridge_equiv ... /\ precond_bisim psys n sm' ss'`.*

The universal quantifier is weakened: instead of quantifying over all actions, it quantifies only over those satisfying the precondition. This matches the test runner's behavior, which generates and executes only precondition-satisfying actions.

**Theorem 10.9** (Universal implies preconditioned, `universal_implies_preconditioned`). *`bounded_bisim sys n sm ss` implies `precond_bisim psys n sm ss` for any precondition.*

*Proof.* By induction on `n`. The universal quantifier in `bounded_bisim` specializes to the restricted quantifier in `precond_bisim`. QED.

This theorem is a soundness result: the existing formalization (which quantifies over all actions) is a conservative overapproximation of what the runner actually checks. A system satisfying universal bisimulation automatically satisfies preconditioned bisimulation.

**Theorem 10.10** (Preconditioned runner correspondence, `precond_runner_implies_bisim`). *If the preconditioned runner passes on all valid traces of length `n`, then preconditioned bisimulation holds at depth `n`.*

**Theorem 10.11** (Converse, `precond_bisim_implies_runner`). *If preconditioned bisimulation holds at depth `n`, the preconditioned runner passes on every precondition-valid trace of length `n`.*

Together, Theorems 10.10 and 10.11 establish the preconditioned runner correspondence: the preconditioned runner is sound and complete with respect to preconditioned bisimulation. The precondition-validity requirement in Theorem 10.11 is necessary because the preconditioned runner includes precondition checks in its trace processing; a trace violating preconditions would fail the runner regardless of the bisimulation.

The relationship between the universal and preconditioned versions is strictly one-directional: preconditioned bisimulation is strictly weaker than universal bisimulation. A system may satisfy preconditioned bisimulation (because buggy actions are filtered out by preconditions) while failing universal bisimulation. The gap is by design: preconditions model the intended usage of the system, excluding pathological inputs that the implementation is not required to handle.

---

## 11. Discussion and Related Work

### Process-Algebraic Bisimulation

The logical-observational-game-semantic triangle for bisimulation has deep roots in process algebra. Milner's CCS [33] and Park's bisimulation [38] establish the logical characterization. Hennessy and Milner [22] prove that bisimulation equivalence coincides with modal logic equivalence for image-finite processes, the classical analogue of our observational refinement biconditional. Stirling [44] and Thomas [45] develop game-semantic characterizations of various process equivalences. Our contribution is not the triangle itself but its machine-checked instantiation for a specific testing framework with crash-recovery extensions. The bounded depth restriction is both a limitation and a feature: it matches the finite-depth nature of property-based testing, where the test runner explores traces up to a configurable depth.

### Property-Based Testing

De Vries's `quickcheck-lockstep` [12] for Haskell introduced the lockstep paradigm with opaque handles and GADT-indexed actions. Our formalization captures the essence of this approach while abstracting away the Haskell-specific type system features. The `proptest-state-machine` crate [40] provides the Rust-side infrastructure for sequential state-machine testing. Hedgehog [20] and Hypothesis [31] offer similar capabilities in Haskell and Python. None of these frameworks provide formal guarantees beyond the operational claim that "the test checks what it checks." Our runner correspondence theorem (Theorem 3.2) is the first machine-checked proof that the runner's operational behavior corresponds to a declarative mathematical property.

### Crash-Recovery Testing and Verification

Jepsen [26] is the de facto standard for empirical crash-recovery testing of distributed databases. It injects crash faults and checks linearizability, but provides no formal guarantees about the completeness of its exploration. Our crash bisimulation (Section 7) and crash-transparent elimination (Section 8) formalize the conditions under which crash exploration is complete.

Perennial [9] provides full crash-recovery verification in Coq, with crash Hoare logic and recovery procedures proved correct for systems like GoJournal [8]. This is a fundamentally different approach: Perennial proves total correctness for a specific implementation, while our framework provides testing guarantees parameterized by exploration depth. The two approaches occupy complementary niches: Perennial for critical infrastructure where full verification is justified, and our approach for the much larger class of systems where property-based testing is the pragmatic choice.

CSPEC [10] and CrashMonkey [35] provide crash-simulation frameworks at the systems level. Pillai et al. [39] study crash vulnerabilities in file systems empirically. Our crash-transparent elimination theorem (Theorem 8.5) provides the formal justification for the pruning heuristics these tools employ.

### Logical Relations and Abstraction Theorems

The bridge is a logical relation in the sense of Reynolds [42]. The observational refinement biconditional (Theorem 4.6) is the analogue of the abstraction theorem: the bridge determines what is observable, and bisimulation guarantees that no observation through the bridge API can distinguish the SUT from the model. The sum, product, option, and list lifts are the standard type-constructor actions on logical relations, and the refinement preorder on bridges corresponds to the containment ordering on relations.

The connection to parametricity [47] is suggestive but imperfect. In Reynolds' setting, the logical relation is induced by type abstraction; in ours, it is explicitly specified by the user. This explicit specification is both a strength (it accommodates opaque handles and partial observations) and a limitation (it requires the user to correctly specify what should be observed).

### Game Semantics

Abramsky, Jagadeesan, and Malacaria [1] develop game semantics for PCF, where full abstraction is the central result: two terms are observationally equivalent if and only if they have the same set of complete plays. Our Theorem 5.5 is a finitary, bounded-depth analogue: bounded bisimulation fails if and only if the Attacker has a winning strategy of bounded depth. The restriction to deterministic step functions simplifies the game: strategies are paths rather than trees, and the Attacker's choices are actions rather than arbitrary moves.

### Limitations

Our formalization assumes deterministic step functions: `step_model` and `step_sut` are total functions, not relations. This excludes nondeterministic systems, where the SUT may produce different outputs on the same input. Extending to nondeterminism would require alternating quantifiers in the bisimulation definition and a more complex game structure.

The Lean proofs are not extracted to executable code. The bridge between the formalization and the Rust implementation is semantic: the Lean definitions correspond to the Rust types by construction, but there is no mechanical extraction or linking. Bridging this gap would require either a verified compiler from Lean to Rust or a formalization of the Rust implementation in Lean, both of which are beyond the scope of this work.

Bounded bisimulation covers only finite-depth interaction. For infinite-depth properties (such as liveness or fairness), the coinductive `lockstep_bisim` is the appropriate notion, but our testing framework can only explore finite prefixes.

---

## 12. Conclusion

We have presented three equivalent characterizations of bounded bisimulation for lockstep property-based testing:

1. **Logical**: bounded bisimulation as a recursive predicate, parameterized by a bridge algebra that determines observational granularity.
2. **Observational**: bounded bisimulation as trace-level indistinguishability, connected to the runner's operational behavior by a biconditional correspondence.
3. **Game-semantic**: failure of bounded bisimulation as the existence of a valid Attacker winning strategy, where the strategy is a concrete, inspectable witness encoding the minimal failing test case.

All three characterizations extend uniformly to crash-recovery systems, with the crash-aware Attacker gaining two additional moves (invariant violation and crash injection). We proved crash-transparent elimination, a strategy dominance result that justifies exponential pruning of the crash-interleaving search space. We established the strictness of the consistency hierarchy from bounded bisimulation (linearizability) through session bisimulation to convergent bisimulation (eventual consistency), using concrete counterexample systems.

The formalization comprises 20 Lean 4 files containing 182 machine-checked theorems with zero `sorry`. Every biconditional in this paper is a named theorem that typechecks against Lean 4's kernel. The three biconditionals — `runner_bounded_bisim_equiv`, `observational_refinement_equiv`, and `bisim_game_semantic` — together with their crash-recovery extensions `crash_bisim_game_semantic` and `crash_witness_transparent_simplify`, constitute a coherent metatheory for property-based testing. Each claim is a theorem rather than a belief, and each proof direction carries distinct computational content: soundness (the system satisfies a guarantee), completeness (the guarantee implies the system property), and concreteness (failures have inspectable witnesses).
