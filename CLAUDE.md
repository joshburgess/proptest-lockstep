# proptest-lockstep

Lockstep-style stateful property testing for Rust. A reimagination of Haskell's `quickcheck-lockstep` (Edsko de Vries) using Rust's type system. Includes 182 machine-checked Lean 4 theorems.

## Build & Test

```bash
cargo check                          # type-check everything
cargo test --lib                     # unit tests (38 tests)
cargo test                           # everything (lib + examples)

# Feature-gated modules
cargo check --features concurrent       # Shuttle concurrent testing
cargo check --features concurrent-loom  # loom exhaustive schedule testing
cargo check --features async            # async SUT support
cargo test --features concurrent        # lib tests including concurrent + linearizability + DPOR

# Formal verification
cd formal_verification && lake build    # 20 Lean files, 182 theorems, zero sorry

# Benchmarks
cargo bench --features concurrent --bench linearizability

# Examples (27 total)
cargo test --example kv_store                                    # simple lockstep
cargo test --example file_system                                 # opaque handles + GVar
cargo test --example file_system_derived                         # auto-derived bridges
cargo test --example treiber_stack                               # lock-free stack
cargo test --example treiber_stack --features concurrent         # concurrent linearizability
cargo test --example crossbeam_queue                             # real crate testing
cargo test --example evmap_test                                  # eventual consistency on real crate
cargo test --example bug_detection                               # 3 bugs caught
cargo test --example crash_recovery_log                          # crash-recovery
cargo test --example batched_log                                 # batched crash-recovery
cargo test --example guided_shrinking                            # bisimulation-guided minimization
cargo test --example certified_synthesis                         # proof-carrying bridges
```

## Project Structure

```
src/
├── lib.rs              re-exports, prelude
├── model.rs            LockstepModel trait (user-facing)
├── bridge.rs           LockstepBridge: Transparent, Opaque, ResultBridge, TupleBridge, etc.
├── runner.rs           proptest-state-machine bridge (LockstepRef, LockstepSut)
├── action.rs           AnyAction trait (existential boundary)
├── phase.rs            Phase GAT: Symbolic/Concrete, SymVar/ConVar
├── witness.rs          Is<A,B> type equality witness (GADT simulation)
├── op.rs               Op<A,B> trait: OpId, OpFst, OpSnd, OpOk, OpErr, OpComp
├── env.rs              TypedEnv: heterogeneous variable environment (Send)
├── gvar.rs             GVar<X,Y,O>: generalized variable with typed projection chains
├── theory.rs           Documentation of the metatheory + Lean theorem index
├── concurrent.rs       Concurrent: crash-absence, linearizability, DPOR, ConflictMaximizing, loom
├── async_support.rs    Async SUT support (feature: async)
├── invariant.rs        InvariantModel: shared per-step state invariant checking
├── crash_recovery.rs   CrashRecoveryModel: crash injection + recovery verification
├── commutativity.rs    CommutativitySpecModel: test commutativity specifications
├── compositional.rs    Compositional testing: verify subsystems independently, compose guarantees
├── eventual.rs         EventualConsistencyModel: convergence checking after sync
├── session.rs          SessionConsistencyModel: per-session ordering guarantees
├── effects.rs          EffectModel + ConflictAlgebra: O(1) static commutativity via effects
├── differential.rs     DifferentialBridgeModel: meta-testing of bridge precision
├── shrinking.rs        Bisimulation-guided trace minimization
├── coverage.rs         CoverageGuidedModel: semantic coverage using model state
├── contracts.rs        RefinementGuard: runtime contract monitoring via bridges
└── certified.rs        CertifiedLockstepBridge: proof-carrying bridge marker trait

proptest-lockstep-derive/
└── src/lib.rs          #[lockstep_actions] proc macro with polynomial bridge derivation

formal_verification/FormalVerification/
├── Bridge.lean              Bridge algebra, lifts, decidability (23 defs/thms)
├── BridgeRefinement.lean    Refinement preorder, monotone lifts (11 defs/thms)
├── CertifiedSynthesis.lean  Certified bridge constructors + soundness (12 defs/thms)
├── Compositional.lean       Product systems, compositional bisim (4 thms)
├── CommutativitySpec.lean   Commutativity spec soundness (6 defs/thms)
├── CrashRecovery.lean       Crash bisimulation (9 defs/thms)
├── DerivedBridge.lean       Derivation monotonicity (5 thms)
├── DPOR.lean                Model commutativity, swap soundness (9 defs/thms)
├── EffectLattice.lean       Effect algebra, R/W conflicts (8 defs/thms)
├── EventualConsistency.lean Convergent bisimulation (8 defs/thms)
├── Invariant.lean           Invariant bisimulation (8 defs/thms)
├── Linearizability.lean     Linearizability definition + properties (8 defs/thms)
├── Lockstep.lean            Bounded bisimulation (7 defs/thms)
├── ObservationalRefinement.lean  Observational refinement biconditional (8 defs/thms)
├── OpaqueDetection.lean     Delayed opaque handle detection (8 thms)
├── Precondition.lean        Preconditioned bisimulation (8 defs/thms)
├── Runner.lean              Runner correspondence biconditional (7 defs/thms)
├── SessionConsistency.lean  Session bisimulation (7 defs/thms)
├── Soundness.lean           Soundness theorems (6 thms)
└── TestingCompleteness.lean Testing completeness (3 thms)

examples/ (27 examples)
├── kv_store.rs              Simple test (transparent types, no handles)
├── file_system.rs           Full test (opaque handles, GVar projections, composed bridges)
├── file_system_derived.rs   Same as above with auto-derived bridges
├── kv_concurrent.rs         Concurrent: crash-absence + linearizability + ConflictMaximizing
├── fs_concurrent.rs         Concurrent: linearizability with opaque handles
├── treiber_stack.rs         Lock-free stack (AtomicPtr + CAS)
├── bounded_channel.rs       Bounded MPMC channel
├── concurrent_counter.rs    AtomicU64 with CAS operations
├── lru_cache.rs             LRU cache with eviction
├── crossbeam_queue.rs       Real crate: crossbeam ArrayQueue + SegQueue
├── scc_hashmap.rs           Real crate: scc::HashMap
├── dashmap_test.rs          Real crate: dashmap::DashMap
├── evmap_test.rs            Real crate: evmap (eventual consistency)
├── bug_detection.rs         3 intentional bugs caught by the framework
├── crash_recovery_log.rs    Write-ahead log with crash injection
├── batched_log.rs           Batched log with flush/crash window
├── eventual_cache.rs        Eventually-consistent cache
├── crdt_counter.rs          CRDT G-Counter (3 replicated nodes)
├── session_kv.rs            Multi-session KV with read-your-writes
├── commutativity_spec.rs    KV commutativity specification testing
├── effect_commutativity.rs  Effect-indexed commutativity (R/W effects)
├── compositional_test.rs    Counter + Logger composed testing
├── differential_bridge.rs   Differential bridge testing (coarse vs fine)
├── guided_shrinking.rs      Bisimulation-guided trace minimization
├── coverage_guided.rs       Model-coverage-guided generation
├── refinement_contract.rs   Runtime contract monitoring
└── certified_synthesis.rs   Proof-carrying bridge certificates

benches/
└── linearizability.rs       Criterion benchmarks for DPOR + linearizability
```

## Extension Architecture

```
LockstepModel (core)
  └── InvariantModel (shared per-step state predicates)
        ├── CrashRecoveryModel       (crash injection + recovery verification)
        ├── CommutativitySpecModel   (test commutativity specifications)
        ├── EventualConsistencyModel (convergence after sync)
        └── SessionConsistencyModel  (per-session ordering guarantees)

Standalone extensions (no trait hierarchy):
  ├── EffectModel + ConflictAlgebra  (O(1) static commutativity)
  ├── DifferentialBridgeModel        (meta-testing of bridge precision)
  ├── CoverageGuidedModel           (semantic coverage guidance)
  ├── CertifiedLockstepBridge       (proof-carrying bridge marker)
  └── RefinementGuard               (runtime contract monitoring)
```

## What the proc macro generates

From `#[lockstep_actions]` annotated action structs, the macro generates:

1. **GADT enum** with `Is<>` type equality witnesses per variant
2. **Visitor trait** with exhaustive per-action methods
3. **Typed constructor functions** (`new_open`, `new_write`, etc.)
4. **Boxed constructors** (`open`, `write`, etc.) returning `Box<dyn AnyAction>`
5. **`run_sut` on the GADT** using `proof.cast()` — the blog-post pattern
6. **`AnyAction` impl** with auto-generated:
   - `check_bridge` — dispatches to the correct `LockstepBridge` per variant
   - `check_model_bridge` — model-to-model comparison for DPOR
   - `store_model_var` / `store_sut_var` — downcasts and inserts into TypedEnv
7. **Typed interpreter traits** (`ModelInterp`, `SutInterp`)
8. **`dispatch_model` / `dispatch_sut` / `dispatch_sut_send`** — helpers
9. **Polynomial bridge derivation** — auto-derives bridge from `real_return` + `model_return` + `opaque_types`

## Key Design Decisions

- `Phase::Var<T>` GAT has no `Clone + Debug` bounds (relaxed for `ConVar` compatibility)
- `OpComp<F, G, B>` has 3 type params (intermediate type `B` explicit for Rust's type inference)
- `TypedEnv` uses `Box<dyn Any + Send>` — values must be `Send` for concurrent testing
- `LockstepSut` carries its own model copy and re-runs it per step — no shared mutable state
- `Is<A,B>` uses `PhantomData<fn(A) -> B>` for sound variance; `lift` is `pub(crate)`
- Concurrent: `ModelState: PartialEq` required for DPOR and ConflictMaximizing
- DPOR: `check_model_bridge` for symmetric comparison; sleep sets inherit from parent/siblings
- ConflictMaximizing: approximation — commutativity checked against post-prefix state
- Loom: action generation outside `loom::model` for deterministic replay

## Conventions

- Unsafe encapsulated in `witness.rs` only — users never write unsafe
- Tests in `#[cfg(test)] mod tests` within each module
- Use `cargo expand --example kv_store` to inspect proc macro output
- Lean formalization: zero `sorry`, all proofs machine-checked
