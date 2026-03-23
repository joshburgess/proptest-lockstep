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
