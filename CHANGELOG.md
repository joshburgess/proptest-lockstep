# Changelog

## 0.1.0

Initial release.

### Core

- GADT simulation via `Is<A, B>` type equality witnesses
- Composable bridge algebra (`ResultBridge`, `TupleBridge`, `Opaque`, `Transparent`, ...)
- Typed projection chains via `GVar` + `Op` trait
- Phase distinction via GATs (`SymVar<T>` during generation, concrete values during execution)
- `BudgetExceeded` configuration

### Concurrent Testing

- Crash-absence testing via [Shuttle](https://github.com/awslabs/shuttle) (`concurrent` feature)
- Linearizability checking via `ConcurrentLockstepModel`
- Exhaustive schedule enumeration via [loom](https://github.com/tokio-rs/loom) (`concurrent-loom` feature)
- DPOR (Dynamic Partial-Order Reduction): prunes redundant interleavings via model-as-commutativity-oracle
- ConflictMaximizing scheduling: model-guided scheduling for maximum contention
- `LinearizabilityStats`: reports interleavings tried/pruned

### Extensions

- **Crash-recovery testing** (`crash_recovery.rs`): random crash injection with recovery verification
- **Eventual consistency** (`eventual.rs`): tests systems that converge after sync but allow stale reads
- **Session consistency** (`session.rs`): per-session ordering guarantees (read-your-writes, monotonic reads)
- **Commutativity specs** (`commutativity.rs`): tests that declared commutativity specifications are correct
- **Effect-indexed commutativity** (`effects.rs`): O(1) static commutativity via read/write effect annotations
- **Compositional testing** (`compositional.rs`): test subsystems independently, compose the guarantees via product bisimulation
- **Differential bridge testing** (`differential.rs`): meta-testing that detects overly-coarse bridges hiding real discrepancies
- **Bisimulation-guided shrinking** (`shrinking.rs`): minimize counterexamples using bisimulation structure (failure depth + action relevance)
- **Model-coverage-guided generation** (`coverage.rs`): semantic coverage using model state as the coverage oracle
- **Runtime contracts** (`contracts.rs`): shadow SUT with model at runtime, collect violations without crashing
- **Certified bridge synthesis** (`certified.rs`): proof-carrying bridges with `CertifiedLockstepBridge` marker trait

### Proc Macro (`derive` feature)

- `lockstep_actions` attribute macro for declaring action types
- Polynomial bridge derivation: bridges auto-derived from `real_return` + `model_return` + `opaque_types` (the `bridge` attribute is optional)
- `check_model_bridge` generation: symmetric model-to-model comparison for DPOR precision
- `opaque_types = { R => M }` attribute for declaring opaque type mappings
- `dispatch_sut_send` generation for concurrent dispatch

### Formal Verification

- 236 machine-checked Lean 4 theorems across 34 files, zero `sorry`
- Theoretical chain: `runner passes ↔ bounded_bisim ↔ observational refinement`
- DPOR soundness, linearizability, opaque handle detection, testing completeness
- Bridge algebra: decidability, refinement ordering, monotone lifts, derived bridge preservation
- Crash bisimulation, convergent bisimulation, session bisimulation, compositional bisimulation
- Effect lattice soundness, commutativity spec soundness, certified bridge synthesis

### Case Studies (27 examples)

- Real data structures: Treiber stack, bounded channel, concurrent counter, LRU cache
- Real crates from crates.io: crossbeam-queue (ArrayQueue + SegQueue), scc::HashMap, dashmap::DashMap, evmap, sled, crdts
- Bug detection: 3 intentional bugs caught (off-by-one, stale length, wrong eviction)
- Crash-recovery: WAL (immediate flush), batched log (deferred flush)
- Eventual consistency: lazy cache, CRDT G-Counter, evmap
- Other extensions: session KV, commutativity spec, effect commutativity, compositional counter+logger, differential bridge, guided shrinking, coverage-guided, runtime contracts, certified synthesis

### Benchmarks

- Criterion benchmarks for DPOR pruning ratio, commutativity check cost, linearizability scaling
