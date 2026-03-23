# Papers to Write

## What This Project Is

proptest-lockstep is the only property-based testing framework with machine-checked metatheory. No other PBT framework — QuickCheck, Hedgehog, proptest, quickcheck-lockstep — has formal proofs of its soundness. This project has 376 of them, zero sorry, across 33 Lean 4 files, surviving 12 rounds of adversarial review with zero remaining issues.

The formalization covers territory no one has formalized before:

- **Three characterizations of bisimulation** (logical, observational, game-semantic) — each proved equivalent. Process algebraists have these informally; we have them machine-checked for a testing framework.

- **Crash-recovery PBT soundness** — the first formal proof that crash injection + recovery testing is sound. This sits between Jepsen (empirical) and Perennial (full verification) in a gap no one else occupies.

- **Session-aware DPOR** with proved history commutativity across sessions — a testing optimization no other framework has, grounded in a theorem.

- **Polynomial bridge algebra** with structural refinement inducing bridge refinement via natural transformation — the categorical foundation that makes "bridges as logical relations" a theorem, not a metaphor.

- **Game-semantic witness extraction** for both bounded and crash bisimulation — concrete Attacker strategies that ARE the minimal failing test cases.

## Paper 1: ICFP Functional Pearl — "Bridges as Logical Relations"

**Venue:** ICFP (International Conference on Functional Programming)

**Story:** The bridge algebra is a type-indexed family of logical relations preserved by type constructors. The polynomial functor structure makes bridge derivation mechanizable (the proc macro). The Lean formalization proves the fundamental theorem, refinement ordering, and naturality of coarsening.

**Key results to highlight:**
- Bridge algebra as polynomial-functor-indexed logical relations
- `shape_refines_bridge_refines` — structural refinement induces bridge refinement
- `coarsen_natural` — coarsening is a natural transformation between polynomial functors
- `refines_strengthen_bisim` — finer bridges give stronger bisimulation guarantees
- `product_bisim_iff` — compositional testing is a biconditional
- The proc macro derives bridges from type structure (polynomial composition)

**Narrative:** "Just as `deriving(Eq)` gives structural equality, `#[derive(LockstepBridge)]` gives structural observation. The bridge algebra is the generic programming of logical relations."

**Estimated writing time:** 3-4 months.

## Paper 2: POPL — "Formal Verification of Lockstep Testing"

**Venue:** POPL (Principles of Programming Languages)

**Story:** Comprehensive formalization of property-based testing metatheory. The breadth is the contribution: 376 definitions covering bisimulation, observational refinement, DPOR, crash recovery, session consistency, compositional testing, and game semantics — all machine-checked with zero sorry.

**Key results to highlight:**
- `runner_bounded_bisim_equiv` — runner passes ↔ bounded bisimulation (biconditional)
- `observational_refinement_equiv` — bounded bisimulation ↔ observational indistinguishability
- `bisim_game_semantic` — ¬bounded_bisim ↔ ∃ winning Attacker strategy
- `crash_bisim_game_semantic` — same for crash-recovery systems (four branches)
- `crash_session_obs_equiv_iff` — crash-session bisimulation ↔ crash-interleaved observational equivalence
- `dpor_swap_sound` + `sleep_set_equiv` — DPOR soundness with sleep set biconditional
- `apply_session_write_commute` — session history updates commute across sessions
- Consistency hierarchy with both gaps witnessed by Lean counterexamples

**Narrative:** "We machine-checked the metatheory of property-based testing. The formalization connects three characterizations of bisimulation (logical, observational, game-semantic) and proves soundness for crash-recovery, session consistency, and concurrent linearizability testing."

**Estimated writing time:** 2-3 months.

## Paper 3: OOPSLA Tool Track — "proptest-lockstep: Practical Stateful PBT for Rust"

**Venue:** OOPSLA (Object-Oriented Programming, Systems, Languages & Applications)

**Story:** The Rust implementation: 29 modules, 30 examples, concurrent linearizability testing with DPOR, 6 real crates tested (crossbeam, evmap, dashmap, scc, sled), crash-recovery testing, session consistency, effect-indexed commutativity, bisimulation-guided shrinking, model-coverage-guided generation, incremental compositional testing with bridge precision tracking.

**Key results to highlight:**
- 30 working examples covering all features
- 6 real-world crate case studies with bugs found
- DPOR + ConflictMaximizing for concurrent linearizability
- Crash-recovery testing (WAL example, batched log)
- Session consistency testing (multi-session KV)
- `IncrementalComposition` with `BridgePrecision` auto-invalidation
- Criterion benchmarks for linearizability checking
- The proc macro: `#[lockstep_actions]` with polynomial bridge derivation

**Narrative:** "proptest-lockstep is the most complete lockstep testing framework in any language. It tests 6 real Rust crates, catches real bugs, and its metatheory is machine-checked in Lean 4."

**Estimated writing time:** 1-2 months.

## Paper Priority

1. **ICFP Pearl** (strongest story, self-contained)
2. **OOPSLA Tool Track** (most practical impact)
3. **POPL** (most comprehensive, benefits from the other two being written first)

## Project Stats (Current)

- 376 Lean definitions (33 files, zero sorry)
- 29 Rust modules, 30 examples
- 6 real crates tested
- 78 PRs merged
- 12 rounds of adversarial review
- 3 characterizations of bisimulation (logical, observational, game-semantic)
- 5 genuine hard theorems verified by research critic
