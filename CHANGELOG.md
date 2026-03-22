# Changelog

## 0.4.0

### Formal Verification

- **182 machine-checked Lean 4 theorems** across 20 files, zero `sorry`
- Complete theoretical chain: `runner passes ↔ bounded_bisim ↔ observational refinement`
- DPOR soundness, linearizability, opaque handle detection, testing completeness
- Bridge algebra: decidability, refinement ordering, monotone lifts, derived bridge preservation
- Crash bisimulation, convergent bisimulation, session bisimulation, compositional bisimulation
- Effect lattice soundness, commutativity spec soundness, certified bridge synthesis

### New Extensions

- **Crash-recovery testing** (`crash_recovery.rs`) — random crash injection with recovery verification. First formally verified crash-recovery PBT framework.
- **Eventual consistency** (`eventual.rs`) — tests systems that converge after sync but allow stale reads. First formally verified EC PBT framework.
- **Session consistency** (`session.rs`) — per-session ordering guarantees (read-your-writes, monotonic reads). First formally verified session consistency PBT framework.
- **Commutativity specs** (`commutativity.rs`) — tests that declared commutativity specifications are correct. First formally verified commutativity spec PBT framework.
- **Effect-indexed commutativity** (`effects.rs`) — O(1) static commutativity via read/write effect annotations, replacing the O(n²) dynamic oracle.
- **Compositional testing** (`compositional.rs`) — test subsystems independently, compose the guarantees via product bisimulation.
- **Differential bridge testing** (`differential.rs`) — meta-testing that detects overly-coarse bridges hiding real discrepancies.
- **Bisimulation-guided shrinking** (`shrinking.rs`) — minimize counterexamples using bisimulation structure (failure depth + action relevance).
- **Model-coverage-guided generation** (`coverage.rs`) — semantic coverage using model state as the coverage oracle.
- **Runtime contracts** (`contracts.rs`) — shadow SUT with model at runtime, collect violations without crashing.
- **Certified bridge synthesis** (`certified.rs`) — proof-carrying bridges with `CertifiedLockstepBridge` marker trait.

### Proc Macro

- **Polynomial bridge derivation** — bridges auto-derived from `real_return` + `model_return` + `opaque_types`. The `bridge` attribute is now optional.
- **`check_model_bridge`** generation — symmetric model-to-model comparison for DPOR precision.
- **`opaque_types = { R => M }`** attribute for declaring opaque type mappings.

### Case Studies (27 examples)

- **Real data structures**: Treiber stack, bounded channel, concurrent counter, LRU cache
- **Real crates from crates.io**: crossbeam-queue (ArrayQueue + SegQueue), scc::HashMap, dashmap::DashMap, evmap
- **Bug detection**: 3 intentional bugs caught (off-by-one, stale length, wrong eviction)
- **Crash-recovery**: WAL (immediate flush), batched log (deferred flush)
- **Eventual consistency**: lazy cache, CRDT G-Counter, evmap (real crate)
- **Other extensions**: session KV, commutativity spec, effect commutativity, compositional counter+logger, differential bridge, guided shrinking, coverage-guided, runtime contracts, certified synthesis

### Benchmarks

- Criterion benchmarks for DPOR pruning ratio, commutativity check cost, linearizability scaling

## 0.3.0

### Breaking Changes

- **`ModelState: PartialEq` required for all concurrent entry points.** Enables DPOR and `ConflictMaximizing`.

### Research Features

- **DPOR** — prunes redundant interleavings via model-as-commutativity-oracle
- **ConflictMaximizing** — model-guided scheduling for maximum contention
- **LinearizabilityStats** — reports interleavings tried/pruned

## 0.2.0

- Linearizability checking via `ConcurrentLockstepModel`
- Loom support (`concurrent-loom` feature)
- `dispatch_sut_send` proc macro generation
- `BudgetExceeded` configuration

## 0.1.0

- Initial release: GADT simulation, bridge algebra, typed projections, Phase GAT, concurrent crash-absence testing via Shuttle
