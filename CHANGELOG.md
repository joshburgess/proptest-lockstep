# Changelog

## 0.3.0

### Breaking Changes

- **`ModelState: PartialEq` required for all concurrent entry points.** This enables DPOR (dynamic partial-order reduction) and `ConflictMaximizing` split strategy. Most model states already derive `PartialEq` — add `#[derive(PartialEq)]` to your model state struct if needed.

### Research Features

- **Dynamic partial-order reduction (DPOR).** The linearizability checker automatically detects commuting operations by running both orderings against the model (using `PartialEq` for sound state comparison), and uses sleep sets to prune redundant interleavings. Novel application of Flanagan & Godefroid (2005) to property-based testing.

- **Model-guided scheduling (`ConflictMaximizing`).** New `SplitStrategy::ConflictMaximizing` variant uses the model as a semantic oracle to place conflicting operations on different branches, maximizing contention. No precedent in the concurrency testing literature.

- **`LinearizabilityStats`** — reports interleavings tried, pruned by DPOR, and commutativity checks performed. Printed to stderr after each successful linearizability check.

### Other Changes

- Unified split logic via `split_remaining_with_ids` — eliminates duplicated split code across Shuttle and loom paths.
- `ConflictMaximizing` supported in all concurrent entry points (crash-absence and linearizability, Shuttle and loom).

## 0.2.0

- Linearizability checking via `ConcurrentLockstepModel` extension trait
- Loom support (`concurrent-loom` feature)
- `dispatch_sut_send` proc macro generation
- `BudgetExceeded` configuration
- `kv_concurrent` and `fs_concurrent` examples

## 0.1.0

- Initial release: GADT simulation, bridge algebra, typed projections, Phase GAT, concurrent crash-absence testing via Shuttle
