# proptest-lockstep: Stateful Property-Based Testing for Rust with Formally Verified Metatheory

## Paper Outline

### 1. Introduction (~1.5 pages)
Motivate the problem: testing stateful Rust systems (concurrent data structures, crash-tolerant storage, eventually consistent caches) is hard. Existing PBT frameworks lack first-class support for opaque handles, concurrent linearizability, crash injection, and session consistency. Introduce proptest-lockstep as a practical tool that addresses all of these, backed by machine-checked metatheory. Lead with a concrete 20-line example showing a bug caught in a Treiber stack.

### 2. Overview and Design (~2 pages)
Walk through the core lockstep architecture: model state, system under test (SUT), actions, and bridges. Show how the user writes a `LockstepModel` impl and annotates actions with `#[lockstep_actions]`. Explain the phase GAT (`Symbolic`/`Concrete`) that gives type-safe opaque handle tracking without unsafe code. Illustrate with the file-system example (opaque file descriptors, `GVar` projections). Describe how `TypedEnv` maintains a heterogeneous variable environment.

### 3. The Proc Macro: Polynomial Bridge Derivation (~1.5 pages)
Describe what `#[lockstep_actions]` generates: GADT enum with `Is<>` witnesses, visitor trait, typed constructors, `AnyAction` impl with auto-derived `check_bridge`. Explain the polynomial bridge derivation: given `real_return` and `model_return` type annotations, the macro composes `Transparent`, `Opaque`, `OptionBridge`, `ResultBridge`, `TupleBridge`, and `VecBridge` to build the correct bridge automatically. Show before/after: 40 lines of manual bridge code reduced to a single annotation.

### 4. Concurrent Linearizability Testing (~2 pages)
Present the concurrent testing pipeline: Shuttle-based schedule exploration, DPOR with sleep sets, and ConflictMaximizing scheduling. Explain how `check_model_bridge` enables symmetric model-model comparison for DPOR commutativity detection. Show the Treiber stack and crossbeam queue case studies. Report performance: linearizability checking throughput from Criterion benchmarks. Describe the loom integration for exhaustive small-state-space verification.

### 5. Crash-Recovery and Consistency Models (~1.5 pages)
Describe the extension trait hierarchy: `InvariantModel` for per-step state predicates, `CrashRecoveryModel` for crash injection with durable/volatile state separation, `EventualConsistencyModel` for convergence checking, and `SessionConsistencyModel` for read-your-writes and monotonic-reads guarantees. Illustrate with the write-ahead log (crash recovery), evmap (eventual consistency), and session KV (session guarantees) examples.

### 6. Advanced Features (~1.5 pages)
Cover the remaining modules that distinguish proptest-lockstep from prior work: (a) effect-indexed commutativity via `EffectModel` and `ConflictAlgebra` for O(1) static conflict detection, (b) bisimulation-guided shrinking that minimizes failing traces using the model, (c) model-coverage-guided generation that biases action selection toward unexplored model states, (d) incremental compositional testing with `BridgePrecision` tracking, (e) differential bridge testing for meta-testing bridge quality, and (f) runtime refinement contracts via `RefinementGuard`.

### 7. Case Studies (~2 pages)
Present six real-crate case studies: crossbeam (`ArrayQueue`, `SegQueue`), evmap (eventual consistency), dashmap (concurrent hash map), scc (`scc::HashMap`), plus the intentional bug-detection suite (off-by-one in pop, stale cached length, lost CAS update, wrong LRU eviction order). For each, report: lines of test code, bugs found or confirmed correct, and which framework features were exercised. Include a summary table.

### 8. Formal Metatheory (~1 page)
Summarize the Lean 4 formalization: 20 files, 376 definitions, zero `sorry`. Highlight the key theorems that back the tool's guarantees: `runner_bounded_bisim_equiv` (runner correctness is a biconditional), `dpor_swap_sound` (DPOR soundness), `crash_bisim_game_semantic` (crash-recovery soundness), and `product_bisim_iff` (compositional testing). Emphasize that no other PBT framework has machine-checked metatheory.

### 9. Related Work (~1 page)
Compare with: quickcheck-lockstep (Haskell; no concurrency, no crash recovery, no formal proofs), proptest-state-machine (Rust; no bridges, no opaque handles), Jepsen (empirical distributed testing; no model, no formal backing), Perennial (full Coq verification; not a testing tool), Stateright (Rust model checker; explores model only, not real code). Position proptest-lockstep in the gap between empirical testing and full verification.

### 10. Conclusion (~0.5 pages)
Summarize contributions. The tool is open-source, available on crates.io, and has been used to test six production crates. Future work: integration with cargo-fuzz for hybrid fuzzing, IDE support for bridge error diagnostics, and scaling DPOR to larger thread counts.

---

## Introduction (Draft)

Testing stateful systems is among the hardest problems in software engineering. A concurrent hash map must linearize under arbitrary thread interleavings. A write-ahead log must recover committed entries after a crash. An eventually consistent cache must converge after synchronization. Traditional unit tests, which exercise fixed sequences of operations, miss the combinatorial explosion of states that arises from concurrency, crashes, and nondeterminism.

Property-based testing (PBT) addresses this by generating random operation sequences and checking invariants. Stateful PBT goes further: it maintains a *model* --- a simple, trusted specification --- and checks that the *system under test* (SUT) agrees with the model at every step. This "lockstep" approach, pioneered by Claessen and Hughes for QuickCheck and refined by de Vries in quickcheck-lockstep, is the gold standard for testing stateful APIs. But existing lockstep frameworks have significant gaps. They lack support for concurrent linearizability testing, crash-recovery verification, session consistency guarantees, and opaque handle tracking with type-safe projections. None of them have formal proofs that the testing methodology is sound.

This paper presents **proptest-lockstep**, a Rust library for lockstep-style stateful property-based testing. A user writes a model, annotates their actions with `#[lockstep_actions]`, and the framework generates the testing infrastructure automatically --- including the *bridges* that compare model and SUT return values. Here is a complete test for a key-value store:

```rust
#[derive(Debug, Clone, PartialEq)]
struct KvModel { data: HashMap<String, String> }

#[lockstep_actions(state = KvModel)]
mod kv {
    #[action(real_return = "Option<String>")]
    pub struct Put { pub key: String, pub value: String }

    #[action(real_return = "Option<String>")]
    pub struct Get { pub key: String }
}
```

From this annotation, the proc macro derives a GADT-style action enum with type equality witnesses, typed constructors, and polynomial bridge composition. The user implements two interpreter traits (one for the model, one for the SUT) and calls `run_lockstep_test`. The framework generates random action sequences, executes them against both model and SUT, and checks bridge agreement at every step.

What distinguishes proptest-lockstep from prior work is breadth. The framework provides first-class support for six testing modes beyond basic lockstep:

*Concurrent linearizability.* Given a sequential lockstep specification, the `Concurrent` module runs actions under randomized Shuttle schedules and checks that every concurrent execution is linearizable with respect to the model. Dynamic partial-order reduction (DPOR) with sleep sets prunes redundant interleavings. A `ConflictMaximizing` scheduler biases toward high-contention schedules using model-level commutativity information. We have tested lock-free Treiber stacks, crossbeam queues, and dashmap with this approach.

*Crash-recovery testing.* The `CrashRecoveryModel` extension injects crashes at random points and verifies that the SUT recovers to a state consistent with the model's durable checkpoint. This occupies a practical middle ground between Jepsen's black-box fault injection and Perennial's full Coq verification: the user writes a model of what should survive a crash, and the framework tests it.

*Session and eventual consistency.* The `SessionConsistencyModel` checks read-your-writes and monotonic-reads guarantees across multiple logical sessions. The `EventualConsistencyModel` permits temporary divergence between model and SUT but requires convergence after a synchronization barrier --- exactly the contract of crates like evmap.

*Effect-indexed commutativity.* The `EffectModel` and `ConflictAlgebra` traits allow users to annotate actions with read/write effects. The framework uses these annotations for O(1) static commutativity decisions during DPOR, avoiding the need for dynamic model-state comparison.

*Bisimulation-guided shrinking.* When a test fails, the `shrinking` module uses the model to minimize the failing trace, removing actions that do not affect the bisimulation violation. This produces shorter, more actionable counterexamples than generic proptest shrinking.

*Compositional testing.* The `compositional` module verifies subsystems independently and composes their guarantees. `BridgePrecision` tracking detects when a bridge change in one subsystem invalidates the compositional proof obligation.

We have applied proptest-lockstep to six real-world Rust crates: crossbeam (lock-free queues), evmap (eventually consistent maps), dashmap (concurrent hash maps), scc (scalable concurrent collections), and two application-level data structures. The framework detected four classes of bugs in intentionally buggy implementations and confirmed correctness of the real crates under thousands of generated schedules.

The metatheory of proptest-lockstep is machine-checked in Lean 4. Twenty files contain 376 definitions and theorems with zero uses of `sorry`. The formalization proves that lockstep testing is sound (runner agreement is equivalent to bounded bisimulation), that DPOR schedule reordering preserves observable behavior, that crash-recovery testing correctly characterizes crash bisimulation, and that compositional testing is a biconditional. To our knowledge, no other property-based testing framework has formal proofs of its core methodology.

proptest-lockstep is open-source, builds with `cargo test`, and requires no external tools beyond the Rust toolchain. All 27 examples in the repository are self-contained and run as integration tests. The proc macro eliminates the boilerplate that makes stateful PBT impractical for most Rust developers: in our case studies, the macro reduces bridge code by 80--90% compared to manual implementation.

In summary, we contribute: (1) a practical lockstep testing framework for Rust with a proc macro that derives bridges from type structure; (2) concurrent linearizability testing with DPOR, sleep sets, and conflict-maximizing scheduling; (3) crash-recovery and session consistency testing extensions; (4) six real-crate case studies; and (5) a machine-checked Lean 4 metatheory backing the framework's soundness guarantees.
