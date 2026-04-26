# proptest-lockstep

Lockstep-style stateful property testing for Rust, with **182 machine-checked theorems** in Lean 4.

A reimagination of Haskell's [`quickcheck-lockstep`](https://hackage.haskell.org/package/quickcheck-lockstep) (Edsko de Vries, Well-Typed) using Rust's type system: GATs, type equality witnesses, and composable trait algebras.

## What is lockstep testing?

Write a pure model of your stateful system. Generate random sequences of API calls. Execute each call against both the real system and the model. After every step, compare their outputs. If they disagree, you've found a bug.

## Quick start

```toml
[dev-dependencies]
proptest-lockstep = "0.1"
proptest = "1"
```

```rust
#[proptest_lockstep::lockstep_actions(state = MyModel)]
pub mod actions {
    // Bridges auto-derived from return types. No manual bridge annotations.
    #[action(real_return = "Option<String>")]
    pub struct Get { pub key: String }

    #[action(real_return = "Option<String>")]
    pub struct Put { pub key: String, pub value: String }

    // For opaque handles (different real/model types):
    #[action(
        real_return = "Result<(FileHandle, String), FsErr>",
        model_return = "Result<(MockHandle, String), FsErr>",
        opaque_types = { FileHandle => MockHandle },
    )]
    pub struct Open { pub path: String }
}
```

## Core Features

**Composable bridge algebra.** Bridges describe observability: how to compare real and model outputs. They compose: `ResultBridge<TupleBridge<Opaque<Handle, MockHandle>, Transparent<String>>, Transparent<Err>>`. This is a novel contribution not present in the Haskell original.

**Polynomial bridge derivation.** Bridges are auto-derived from return types. Just declare `real_return`, `model_return`, and `opaque_types`, and the proc macro derives the bridge automatically.

**Certified bridge synthesis.** Every built-in bridge type is linked to a machine-checked Lean proof of correctness via the `CertifiedLockstepBridge` trait.

**GADT simulation via type equality witnesses.** Exhaustive matching with per-arm type refinement through `Is<A, B>` Leibniz equality witnesses.

**Phase distinction via GATs.** `SymVar<T>` during generation, concrete values during execution. The compiler enforces the boundary.

**Typed projection chains.** `GVar::new(var, OpOk).then(OpFst)` extracts a handle from `Result<(Handle, Path), Err>`, compile-time verified, zero runtime cost.

## Consistency Hierarchy

The framework supports a formally verified hierarchy of consistency levels:

```
Linearizability (strongest)
    ⟹ Session Consistency
        ⟹ Eventual Consistency (weakest)
```

| Level | Module | What it checks |
|-------|--------|----------------|
| **Linearizability** | `concurrent.rs` | Every concurrent interleaving matches some sequential model execution |
| **Session consistency** | `session.rs` | Per-session ordering guarantees (read-your-writes, monotonic reads) |
| **Eventual consistency** | `eventual.rs` | After synchronization, SUT converges to model state |

## Extensions

| Extension | Module | What it does |
|-----------|--------|-------------|
| **Crash-recovery** | `crash_recovery.rs` | Random crash injection; verifies SUT recovers correctly from persisted state |
| **Commutativity specs** | `commutativity.rs` | Tests that operations declared as commutative actually commute |
| **Effect lattice** | `effects.rs` | O(1) static commutativity via read/write effect annotations |
| **Compositional testing** | `compositional.rs` | Test subsystems independently, compose the guarantees |
| **Differential bridges** | `differential.rs` | Detect overly-coarse bridges that hide real discrepancies |
| **Guided shrinking** | `shrinking.rs` | Minimize counterexamples using bisimulation structure |
| **Coverage-guided gen** | `coverage.rs` | Semantic coverage using model state as the coverage oracle |
| **Runtime contracts** | `contracts.rs` | Shadow SUT with model at runtime; collect violations without crashing |

## Concurrent Testing

Three levels of concurrent verification, all powered by [Shuttle](https://github.com/awslabs/shuttle):

- **Crash-absence**: verifies no panics/deadlocks under randomized schedules
- **Linearizability**: verifies concurrent results match some sequential model ordering
- **Exhaustive enumeration**: explores all thread schedules via [loom](https://github.com/tokio-rs/loom)

**DPOR (Dynamic Partial-Order Reduction)** automatically prunes redundant interleavings. The model serves as the commutativity oracle.

**ConflictMaximizing scheduling** distributes operations to maximize contention. The model guides the split semantically.

## Formal Verification

**20 Lean 4 files, 182 definitions/theorems, zero `sorry`.**

The formalization proves the complete theoretical chain:

```
runner passes  ↔  bounded bisimulation  ↔  observational refinement
```

Plus: DPOR soundness, linearizability, opaque handle detection, crash-recovery bisimulation, compositional bisimulation, commutativity spec soundness, effect lattice soundness, convergent bisimulation, session bisimulation, certified bridge synthesis, testing completeness, and bridge refinement ordering.

Build the formalization:
```bash
cd formal_verification && lake build   # requires Lean 4 / elan
```

## Examples

27 examples covering every feature:

| Category | Examples |
|----------|----------|
| **Core lockstep** | `kv_store`, `file_system`, `file_system_derived` |
| **Concurrent** | `kv_concurrent`, `fs_concurrent` |
| **Case studies** | `treiber_stack`, `bounded_channel`, `concurrent_counter`, `lru_cache` |
| **Real crates** | `crossbeam_queue`, `scc_hashmap`, `dashmap_test`, `evmap_test` |
| **Bug detection** | `bug_detection` (3 intentional bugs caught) |
| **Crash-recovery** | `crash_recovery_log`, `batched_log` |
| **Eventual consistency** | `eventual_cache`, `crdt_counter` |
| **Other extensions** | `session_kv`, `commutativity_spec`, `effect_commutativity`, `compositional_test`, `differential_bridge`, `guided_shrinking`, `coverage_guided`, `refinement_contract`, `certified_synthesis` |

## Benchmarks

```bash
cargo bench --features concurrent --bench linearizability
```

Criterion benchmarks measuring DPOR pruning effectiveness, commutativity check cost, and linearizability scaling.

## How it compares to Haskell's quickcheck-lockstep

| Aspect | Haskell | Rust |
|--------|---------|------|
| Observability | Manual `ModelValue` GADT | **Composable bridge algebra** (novel) |
| Bridge derivation | None | **Auto-derived from return types** |
| Variable projections | `GVar op f` | `GVar<X,Y,O>` + `Op` trait |
| Phase distinction | HKT | GATs |
| Shrinking | Manual | **Integrated + bisimulation-guided** |
| Concurrent testing | None | **Shuttle + loom + DPOR + ConflictMaximizing** |
| Formal verification | None | **182 Lean 4 theorems** |
| Crash-recovery | None | **Random crash injection with recovery verification** |
| Consistency hierarchy | None | **Linearizability → Session → Eventual** |
| Runtime contracts | None | **Shadow monitoring via bridges** |

## License

Dual licensed under [Apache 2.0](LICENSE-APACHE) or [MIT](LICENSE-MIT).
