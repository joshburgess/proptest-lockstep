# proptest-lockstep

Lockstep-style stateful property testing for Rust.

A reimagination of Haskell's [`quickcheck-lockstep`](https://hackage.haskell.org/package/quickcheck-lockstep) (Edsko de Vries, Well-Typed) using Rust's type system — GATs, type equality witnesses, and composable trait algebras.

## What is lockstep testing?

Write a pure model of your stateful system. Generate random sequences of API calls. Execute each call against both the real system and the model. After every step, compare their outputs. If they disagree, you've found a bug.

The framework handles:
- **Generation** — random action sequences with dependent variables
- **Shrinking** — automatic via proptest, no manual shrinker needed
- **Observability** — composable bridges for comparing opaque handles
- **Variable tracking** — typed projection chains for compound return types
- **Concurrency** — crash-absence testing (Shuttle), linearizability checking, and exhaustive schedule enumeration (loom)

## Quick start

```toml
[dev-dependencies]
proptest-lockstep = "0.3"
proptest = "1"
```

```rust
use proptest_lockstep::prelude::*;

#[proptest_lockstep::lockstep_actions(state = MyModel)]
pub mod actions {
    #[action(real_return = "Option<String>", bridge = "OptionBridge<Transparent<String>>")]
    pub struct Get { pub key: String }

    #[action(real_return = "Option<String>", bridge = "OptionBridge<Transparent<String>>")]
    pub struct Put { pub key: String, pub value: String }
}
```

Each action declares its return type and a bridge describing how to compare real and model outputs. The proc macro generates a GADT enum, typed interpreter traits, bridge dispatch, and variable storage.

See the examples:
- [`examples/kv_store.rs`](examples/kv_store.rs) — simplest case, all transparent types
- [`examples/file_system.rs`](examples/file_system.rs) — opaque handles with GVar projections
- [`examples/kv_concurrent.rs`](examples/kv_concurrent.rs) — concurrent crash-absence + linearizability
- [`examples/fs_concurrent.rs`](examples/fs_concurrent.rs) — linearizability with opaque handles

## Key features

**Composable bridge algebra.** Describe observability declaratively — `ResultBridge<TupleBridge<Opaque<Handle, MockHandle>, Transparent<String>>, Transparent<Err>>` — and the compiler verifies the types match. This is a novel contribution not present in the Haskell original.

**GADT simulation via type equality witnesses.** Exhaustive matching with per-arm type refinement, achieved through `Is<A, B>` Leibniz equality witnesses carried in enum variants.

**Phase distinction via GATs.** `SymVar<T>` during generation, concrete values during execution. The compiler enforces the boundary.

**Typed projection chains.** `GVar::new(var, OpOk).then(OpFst)` extracts a handle from `Result<(Handle, Path), Err>` — compile-time verified, zero runtime cost.

**Model-side variable resolution.** `resolve_model_gvar` handles the asymmetry when model and SUT types differ for opaque handles.

**Concurrent testing with three levels of verification:**
- **Crash-absence** (`lockstep_concurrent`) — verifies no panics or deadlocks under randomized Shuttle schedules
- **Linearizability** (`lockstep_linearizable`) — verifies concurrent results are consistent with some sequential model execution. Requires implementing `ConcurrentLockstepModel` (one method). Brute-force interleaving checker with configurable budget via `BudgetExceeded`
- **Exhaustive schedule enumeration** via loom (`lockstep_concurrent_loom`, `lockstep_linearizable_loom`) — explores all possible thread schedules

**Dynamic partial-order reduction (DPOR).** The linearizability checker automatically detects commuting operations by running both orderings against the model, and uses sleep sets to prune redundant interleavings. This is a novel application of DPOR to property-based testing — the model serves as the commutativity oracle.

**Model-guided scheduling (`ConflictMaximizing`).** Actions are distributed across branches to maximize contention — operations that don't commute are placed on different threads. The model is used as a semantic oracle to guide the split, a technique with no precedent in the concurrency testing literature.

**Async SUT support.** Test async systems with synchronous models via the `async` feature flag.

## Features

```toml
# Proc macro (enabled by default)
proptest-lockstep = { version = "0.2", features = ["derive"] }

# Concurrent testing via Shuttle (crash-absence + linearizability)
proptest-lockstep = { version = "0.2", features = ["concurrent"] }

# Exhaustive concurrent testing via loom
proptest-lockstep = { version = "0.2", features = ["concurrent-loom"] }

# Async SUT support
proptest-lockstep = { version = "0.2", features = ["async"] }
```

The `concurrent` and `concurrent-loom` features are independent — each provides its own entry points and they can coexist.

## How it compares to Haskell's quickcheck-lockstep

| Aspect | Haskell | Rust |
|--------|---------|------|
| Exhaustive matching | GADT `case` | Generated GADT enum `match` |
| Per-action typed returns | GADT type index | `Is<ConcreteType, R>` witness |
| Observability | Manual `ModelValue` + `Observable` GADTs | **Composable bridge algebra** (novel) |
| Variable projections | `GVar op f` + `Op` DSL | `GVar<X,Y,O>` + `Op<A,B>` trait |
| Phase distinction | HKT (`Symbolic`/`Concrete`) | GATs (`Phase::Var<T>`) |
| Shrinking | Manual `shrinkWithVars` | **Integrated (free via proptest)** |
| Concurrent testing | None | **Shuttle + loom integration** |
| Linearizability checking | None | **Interleaving checker with DPOR** |
| Schedule guidance | None | **Model-guided ConflictMaximizing split** |
| Async support | None | **async_trait support** |

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or [MIT License](LICENSE-MIT) at your option.
