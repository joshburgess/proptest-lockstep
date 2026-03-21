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
- **Concurrency** — crash-absence testing via Shuttle

## Quick start

```toml
[dev-dependencies]
proptest-lockstep = "0.1"
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

See [`examples/kv_store.rs`](examples/kv_store.rs) for the simplest complete example and [`examples/file_system.rs`](examples/file_system.rs) for opaque handles with GVar projections.

## Key features

**Composable bridge algebra.** Describe observability declaratively — `ResultBridge<TupleBridge<Opaque<Handle, MockHandle>, Transparent<String>>, Transparent<Err>>` — and the compiler verifies the types match. This is a novel contribution not present in the Haskell original.

**GADT simulation via type equality witnesses.** Exhaustive matching with per-arm type refinement, achieved through `Is<A, B>` Leibniz equality witnesses carried in enum variants.

**Phase distinction via GATs.** `SymVar<T>` during generation, concrete values during execution. The compiler enforces the boundary.

**Typed projection chains.** `GVar::new(var, OpOk).then(OpFst)` extracts a handle from `Result<(Handle, Path), Err>` — compile-time verified, zero runtime cost.

**Model-side variable resolution.** `resolve_model_gvar` handles the asymmetry when model and SUT types differ for opaque handles.

**Concurrent crash-absence testing.** Shuttle integration with configurable split strategies (`RoundRobin`, `Random`), N-branch support, trace collection on panic, and optional final state checks.

**Async SUT support.** Test async systems with synchronous models via the `async` feature flag.

## Features

```toml
# Proc macro (enabled by default)
proptest-lockstep = { version = "0.1", features = ["derive"] }

# Concurrent testing via Shuttle
proptest-lockstep = { version = "0.1", features = ["concurrent"] }

# Async SUT support
proptest-lockstep = { version = "0.1", features = ["async"] }
```

## How it compares to Haskell's quickcheck-lockstep

| Aspect | Haskell | Rust |
|--------|---------|------|
| Exhaustive matching | GADT `case` | Generated GADT enum `match` |
| Per-action typed returns | GADT type index | `Is<ConcreteType, R>` witness |
| Observability | Manual `ModelValue` + `Observable` GADTs | **Composable bridge algebra** (novel) |
| Variable projections | `GVar op f` + `Op` DSL | `GVar<X,Y,O>` + `Op<A,B>` trait |
| Phase distinction | HKT (`Symbolic`/`Concrete`) | GATs (`Phase::Var<T>`) |
| Shrinking | Manual `shrinkWithVars` | **Integrated (free via proptest)** |
| Concurrent testing | None | **Shuttle integration** |
| Async support | None | **async_trait support** |

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or [MIT License](LICENSE-MIT) at your option.
