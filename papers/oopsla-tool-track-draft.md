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

## 2. Overview and Design

The central abstraction in proptest-lockstep is the **lockstep model**: a pure, easily inspectable specification of the system under test. The user writes a model, defines actions (the API surface to test), and provides *bridges* that relate model return values to SUT return values. The framework generates random action sequences, executes them against both model and SUT in lockstep, and checks bridge agreement at every step.

### 2.1 The LockstepModel Trait

The core interface is a single trait with six methods:

```rust
pub trait LockstepModel: Debug + Clone + 'static {
    type ModelState: Debug + Clone + 'static;
    type Sut: Debug + 'static;

    fn init_model() -> Self::ModelState;
    fn init_sut() -> Self::Sut;
    fn gen_action(state: &Self::ModelState, env: &TypedEnv)
        -> BoxedStrategy<Box<dyn AnyAction>>;
    fn precondition(state: &Self::ModelState, action: &dyn AnyAction,
        env: &TypedEnv) -> bool;
    fn step_model(state: &mut Self::ModelState, action: &dyn AnyAction,
        env: &TypedEnv) -> Box<dyn Any>;
    fn step_sut(sut: &mut Self::Sut, action: &dyn AnyAction,
        env: &TypedEnv) -> Box<dyn Any>;
}
```

The `ModelState` is typically a plain Rust struct --- a `HashMap` for a key-value store, a `Vec` for a stack, a `VecDeque` for a queue. The `Sut` is the real system: a `TreiberStack<i32>`, a `crossbeam_queue::ArrayQueue<i32>`, or a `dashmap::DashMap<String, i32>`. The model is cheap and pure; the SUT may be concurrent, persistent, or networked.

Action generation is state-dependent. The `gen_action` method receives the current model state, allowing the generator to produce only valid actions. For example, a stack test generates `Pop` only when the model is non-empty:

```rust
fn gen_action(state: &StackModel, _env: &TypedEnv)
    -> BoxedStrategy<Box<dyn AnyAction>>
{
    let mut strats: Vec<BoxedStrategy<Box<dyn AnyAction>>> = vec![
        (0i32..100).prop_map(|v| stack::push(stack::Push { value: v })).boxed(),
        Just(stack::is_empty(stack::IsEmpty)).boxed(),
    ];
    if !state.items.is_empty() {
        strats.push(Just(stack::pop(stack::Pop)).boxed());
    }
    proptest::strategy::Union::new(strats).boxed()
}
```

### 2.2 The Bridge Algebra

The bridge is the comparison function that relates model and SUT return values. The core trait is:

```rust
pub trait LockstepBridge {
    type Real;
    type Model;
    type Observed: Debug + PartialEq;
    fn observe_real(r: &Self::Real) -> Self::Observed;
    fn observe_model(m: &Self::Model) -> Self::Observed;
}
```

Each bridge projects a real value and a model value into a common `Observed` type, then compares for equality. The framework provides two primitive bridges and four algebraic lifts:

- **`Transparent<T>`**: model and SUT return the same type `T`; comparison is direct equality. Used for `String`, `i32`, `bool`, error enums.
- **`Opaque<R, M>`**: model and SUT return different types (e.g., `FileHandle` vs `MockHandle`); the observed form is `()`, so the bridge always succeeds. A wrong handle is detected *later*, when using it produces an incorrect observable result.
- **`ResultBridge<OkB, ErrB>`**: lifts bridges over `Result<Ok, Err>`.
- **`TupleBridge<AB, BB>`**: lifts bridges over `(A, B)` pairs.
- **`OptionBridge<B>`**: lifts bridges over `Option<T>`.
- **`VecBridge<B>`**: lifts bridges pointwise over `Vec<T>`.

These compose polynomially. For example, the file-system example's `Open` action returns `Result<(FileHandle, String), FsErr>` from the SUT and `Result<(MockHandle, String), FsErr>` from the model. The bridge is `ResultBridge<TupleBridge<Opaque<FileHandle, MockHandle>, Transparent<String>>, Transparent<FsErr>>` --- the handle is opaque, the path is transparent, and the error is transparent.

### 2.3 Phase GATs and Opaque Handle Tracking

Many stateful APIs return *handles* --- file descriptors, connection IDs, cursors --- that are opaque tokens used in subsequent operations. The model uses surrogate handles (`MockHandle(usize)`) that differ from the real handles (`FileHandle(usize)`). The challenge: how does an action like `Write` refer to a handle returned by a previous `Open`?

proptest-lockstep solves this with a phase-indexed generic-associated-type (GAT) system. The `Phase` trait distinguishes two execution phases:

```rust
pub trait Phase: Clone + Debug + 'static {
    type Var<T: 'static>;
}
```

During *generation* (`Symbolic` phase), variables are opaque tokens (`SymVar<T>`) that carry only an ID. During *execution* (`Concrete` phase), variables hold real values (`ConVar<T>`). The `GVar<X, Y, O>` type combines a symbolic variable with a projection chain: if `Open` returns `Result<(FileHandle, String), FsErr>`, a subsequent `Write` can refer to just the `FileHandle` component via `GVar::new(open_var, OpOk).then(OpFst)`.

The `TypedEnv` is a heterogeneous map (`Box<dyn Any + Send>` values) that stores both model and SUT results, indexed by variable ID. After each step, the runner stores the model result in the model environment and the SUT result in the real environment. When a subsequent action references a `GVar`, the framework resolves it against the appropriate environment, applying the projection chain.

### 2.4 The Runner

The lockstep runner builds on `proptest-state-machine`, which provides the proptest integration (strategy generation, shrinking, test case management). The runner has two components:

- **`LockstepRef`**: the reference state machine. Maintains the model state and model environment. Proptest generates and shrinks action sequences against this.
- **`LockstepSut`**: the concrete state machine. Maintains the SUT, real environment, *and its own copy of the model*. At each step, it runs both model and SUT, checks the bridge, and stores variables.

The SUT side carries its own model copy to avoid shared mutable state between the reference and concrete machines. This means the model executes twice per step --- once for generation/shrinking, once for comparison --- but models are cheap pure data structures, so this is negligible.

A complete lockstep test is launched with a single call:

```rust
run_lockstep_test::<StackLockstep>(1..30);
```

This generates 256 random action sequences (the proptest default) of length 1--30, executes each in lockstep, and reports any bridge mismatch with a shrunk counterexample.

## 3. The Proc Macro: Polynomial Bridge Derivation

The `#[lockstep_actions]` proc macro eliminates the boilerplate that makes lockstep testing impractical by hand. From a module of annotated action structs, it generates seven artifacts: a GADT-style enum, a visitor trait, typed constructors, an `AnyAction` implementation, typed interpreter traits, dispatch functions, and (when possible) automatically derived bridges.

### 3.1 What the Macro Generates

Consider the Treiber stack example:

```rust
#[proptest_lockstep::lockstep_actions(state = StackModel)]
pub mod stack {
    #[action(real_return = "()")]
    pub struct Push { pub value: i32 }

    #[action(real_return = "Option<i32>")]
    pub struct Pop;

    #[action(real_return = "bool")]
    pub struct IsEmpty;
}
```

From this, the macro generates:

**1. GADT enum with type equality witnesses.** Each variant carries an `Is<A, B>` proof that the existentially erased return type matches the concrete one:

```rust
pub enum StackAction {
    Push(Push, Is<(), ()>),
    Pop(Pop, Is<Option<i32>, Option<i32>>),
    IsEmpty(IsEmpty, Is<bool, bool>),
}
```

The `Is<A, B>` type is a Leibniz equality witness: the only constructor is `Is::refl()`, which requires `A == B`. The `cast` method uses an encapsulated `unsafe` transmute that is sound by construction. Users never touch `Is` directly --- it is internal to the generated code.

**2. Visitor trait.** An exhaustive per-action dispatch method that ensures new actions are not forgotten:

```rust
pub trait StackVisitor {
    type Output;
    fn push(&self, action: &Push, proof: Is<(), ()>) -> Self::Output;
    fn pop(&self, action: &Pop, proof: Is<Option<i32>, Option<i32>>) -> Self::Output;
    fn is_empty(&self, action: &IsEmpty, proof: Is<bool, bool>) -> Self::Output;
}
```

**3. Typed constructors.** Both direct (`stack::Push { value: 42 }`) and boxed (`stack::push(stack::Push { value: 42 })`) constructors, the latter returning `Box<dyn AnyAction>` for use in heterogeneous action sequences.

**4. `AnyAction` implementation.** The generated `AnyAction` impl dispatches `check_bridge`, `check_model_bridge`, `store_model_var`, and `store_sut_var` to the correct bridge and type for each variant. This is the existential boundary: all typed logic is monomorphized inside each variant, and `Box<dyn AnyAction>` exists only at the sequence container level.

**5. Typed interpreter traits.** `StackModelInterp` and `StackSutInterp`, each with one method per action. The user implements these to connect the model and SUT to the generated infrastructure.

**6. Dispatch helpers.** `dispatch_model` and `dispatch_sut` functions that downcast a `&dyn AnyAction` to the concrete enum and call the appropriate interpreter method. Also `dispatch_sut_send` for concurrent testing, where results must be `Send`.

### 3.2 Polynomial Bridge Derivation

The most labor-saving feature is automatic bridge derivation. When the user provides `real_return` and `model_return` type annotations, the macro decomposes the type structure and composes bridges from the algebra:

- `()` maps to `UnitBridge`
- `T` (where real and model types are the same) maps to `Transparent<T>`
- `Option<T>` maps to `OptionBridge<derive(T)>`
- `Result<Ok, Err>` maps to `ResultBridge<derive(Ok), derive(Err)>`
- `(A, B)` maps to `TupleBridge<derive(A), derive(B)>`
- `Vec<T>` maps to `VecBridge<derive(T)>`
- Types declared in `opaque_types` map to `Opaque<Real, Model>`

This is a polynomial functor decomposition: every Rust return type that is a composition of `Option`, `Result`, tuples, `Vec`, and base types is automatically bridged. The derivation is monotone in refinement: replacing a component bridge with a finer one produces a finer composite bridge (proved as `derivation_monotone_*` in `DerivedBridge.lean`).

For example, `real_return = "Result<(), i32>"` automatically derives `ResultBridge<Transparent<()>, Transparent<i32>>`. The user writes zero bridge code. For the file-system example with opaque handles, the user can either specify the bridge manually or list opaque types:

```rust
#[action(
    real_return = "Result<(FileHandle, String), FsErr>",
    model_return = "Result<(MockHandle, String), FsErr>",
    opaque_types = { FileHandle = MockHandle },
)]
pub struct Open { pub path: String }
```

The macro derives `ResultBridge<TupleBridge<Opaque<FileHandle, MockHandle>, Transparent<String>>, Transparent<FsErr>>` automatically. In our case studies, this eliminates 80--90% of the bridge code compared to manual implementation.

### 3.3 Before and After

Without the macro, testing a three-action API requires approximately 120 lines of boilerplate: an enum definition, `AnyAction` impl with six method bodies, bridge dispatch logic, variable storage, and type-specific downcasting. With the macro, the same test requires the `#[lockstep_actions]` module (approximately 15 lines) plus two interpreter impls (approximately 20 lines). The macro generates the remaining 85 lines.

## 4. Concurrent Linearizability Testing

Sequential lockstep establishes that the SUT matches the model under single-threaded operation sequences. But many Rust data structures are designed for concurrent access: lock-free stacks, concurrent hash maps, MPMC channels. proptest-lockstep provides a concurrent testing pipeline that verifies *linearizability* --- the gold-standard correctness criterion for concurrent data structures.

### 4.1 Architecture

The concurrent testing pipeline has four stages:

1. **Sequential prefix.** A short sequence of actions executed sequentially to bring the data structure to an interesting state.
2. **Branching.** The remaining actions are split across multiple concurrent branches (threads). The `SplitStrategy` controls the distribution: round-robin, random, or `ConflictMaximizing`.
3. **Concurrent execution.** The branches execute concurrently under Shuttle's randomized scheduler, which explores different thread interleavings.
4. **Linearizability check.** After all branches complete, the framework collects the per-thread operation results and searches for a sequential ordering (a *linearization*) that, when replayed against the model, produces bridge-equivalent results.

The `ConcurrentConfig` controls the test parameters:

```rust
let config = ConcurrentConfig {
    iterations: 100,        // Shuttle schedules to explore
    prefix_len: 3,          // sequential prefix length
    branch_len: 5,          // actions per concurrent branch
    branch_count: 2,        // number of threads
    split_strategy: SplitStrategy::ConflictMaximizing,
    dpor_enabled: true,
    max_interleaving_budget: 1_000_000,
    ..Default::default()
};
```

### 4.2 DPOR with Sleep Sets

The linearizability check must search over all possible orderings of the concurrent operations. For `k` branches of length `n`, the number of interleavings is `(kn)! / (n!)^k`, which grows combinatorially. Dynamic partial-order reduction (DPOR) prunes this search by detecting *commuting* operations: two operations commute at a model state if executing them in either order produces the same results and the same final state.

The commutativity check is performed by the model:

```rust
fn operations_commute(state: &ModelState, a1: &dyn AnyAction, a2: &dyn AnyAction) -> bool
```

Both orderings are executed against a clone of the model state, and the results are compared via `check_model_bridge` --- a symmetric bridge comparison that uses `observe_model` on both sides, avoiding the imprecision of applying `observe_real` to a model value.

When two operations commute, DPOR skips one of the two orderings. Sleep sets further prune: if an operation was already explored from a sibling node in the search tree, it is placed in a sleep set and not re-explored from the current node. Together, DPOR and sleep sets can reduce the search space by orders of magnitude.

The DPOR soundness theorem (`dpor_swap_sound` in `DPOR.lean`) proves that swapping two adjacent commuting operations in a linearization preserves validity. The biconditional `dpor_swap_iff` confirms that commuting operations are fully interchangeable.

### 4.3 ConflictMaximizing Scheduling

The `ConflictMaximizing` split strategy uses the model as a semantic oracle to maximize contention. When distributing actions across branches, it checks each pair of actions for commutativity against the current model state. Non-commuting actions are assigned to *different* branches, so that the scheduler is forced to interleave them. This is an approximation --- commutativity is checked against the post-prefix state, not the state after earlier branch assignments --- but it biases toward high-contention schedules where bugs are most likely to manifest.

### 4.4 Case Study: Treiber Stack

The Treiber stack is the canonical linearizability example. Each `push` and `pop` is a linearization point at the successful CAS. The lockstep model is a simple `Vec<i32>`:

```rust
#[derive(Debug, Clone, PartialEq)]
struct StackModel { items: Vec<i32> }
```

Actions are declared with auto-derived bridges:

```rust
#[proptest_lockstep::lockstep_actions(state = StackModel)]
pub mod stack {
    #[action(real_return = "()")]
    pub struct Push { pub value: i32 }

    #[action(real_return = "Option<i32>")]
    pub struct Pop;
}
```

The concurrent test verifies linearizability under 100 randomized Shuttle schedules with 2 branches of 5 operations each. The test passes, confirming that the CAS-based implementation is linearizable.

### 4.5 Case Study: Crossbeam Queue

The crossbeam `ArrayQueue` is a bounded lock-free MPMC queue with approximately 50 million downloads. We test `push` (returns `Result<(), i32>`), `force_push` (returns `Option<i32>` for the evicted element), `pop`, `len`, and `is_full` against a `VecDeque` model. The bridge for `push` is `ResultBridge<Transparent<()>, Transparent<i32>>`, auto-derived from the type annotation. Under concurrent linearizability testing, all interleavings are consistent with some sequential ordering.

### 4.6 Loom Integration

For exhaustive schedule enumeration (as opposed to Shuttle's randomized approach), proptest-lockstep integrates with loom via the `concurrent-loom` feature flag. Loom explores *all* possible thread schedules up to a depth bound, providing stronger guarantees at the cost of slower execution. The key implementation detail: action generation happens *outside* `loom::model` to ensure deterministic replay during schedule exploration.

## 5. Crash-Recovery and Consistency Models

Beyond basic lockstep and linearizability, proptest-lockstep provides a hierarchy of extension traits for testing increasingly complex consistency guarantees.

### 5.1 Trait Hierarchy

The extension architecture builds on `InvariantModel`, which adds per-step state predicates to the core `LockstepModel`:

```
LockstepModel
  +-- InvariantModel (shared per-step state predicates)
        +-- CrashRecoveryModel       (crash injection + recovery)
        +-- EventualConsistencyModel  (convergence after sync)
        +-- SessionConsistencyModel   (per-session ordering)
        +-- CommutativitySpecModel    (commutativity specifications)
```

Each extension adds a small number of methods (typically 3--5) on top of its parent. The user implements only the extension-specific logic; the framework handles the testing mechanics.

### 5.2 Crash-Recovery Testing

The `CrashRecoveryModel` extension tests systems that must survive crashes. The key insight: the model tracks a *durable state* (what survives a crash) separately from the full model state. After a crash, both model and SUT recover from their persisted state, and testing continues.

The trait adds four methods:

```rust
pub trait CrashRecoveryModel: InvariantModel {
    type DurableState: Debug + Clone + 'static;
    fn model_checkpoint(state: &Self::ModelState) -> Self::DurableState;
    fn model_recover(checkpoint: &Self::DurableState) -> Self::ModelState;
    fn sut_recover(sut: Self::Sut) -> Self::Sut;
}
```

The runner executes a normal lockstep test but probabilistically injects crashes between steps (configurable probability, default 10%). After each crash, it extracts the model's durable checkpoint, recovers the model from it, recovers the SUT by consuming and reconstructing it, and continues testing.

**Case study: Write-ahead log.** The write-ahead log example demonstrates the pattern. The SUT has `committed` entries (on-disk, survive crash) and a `read_count` (in-memory, lost on crash). The model's `DurableState` is `Vec<String>` --- the committed entries. After a crash, the SUT reconstructs from `committed` and resets `read_count` to zero. The model recovers identically. The framework verifies that no committed entries are lost and that the system is functional after recovery.

```rust
impl CrashRecoveryModel for LogLockstep {
    type DurableState = Vec<String>;
    fn model_checkpoint(s: &LogModel) -> Vec<String> { s.entries.clone() }
    fn model_recover(cp: &Vec<String>) -> LogModel {
        LogModel { entries: cp.clone() }
    }
    fn sut_recover(sut: WriteAheadLog) -> WriteAheadLog { sut.recover() }
}
```

The crash-recovery soundness is proved in `CrashRecovery.lean`: if the crash-recovery runner passes, the system satisfies *crash bisimulation*, a strengthening of bounded bisimulation that accounts for crash transitions. The theorem `crash_bisim_double_crash` proves that the system survives multiple consecutive crashes.

### 5.3 Eventual Consistency Testing

Standard lockstep fails on intentionally non-linearizable systems. The `EventualConsistencyModel` extension relaxes the per-step comparison requirement: individual operations may return stale results, but after a *synchronization barrier*, the model and SUT must agree.

```rust
pub trait EventualConsistencyModel: InvariantModel {
    type ObservableState: Debug + PartialEq + Clone + 'static;
    fn sut_sync(sut: &mut Self::Sut) -> Self::ObservableState;
    fn model_sync(state: &Self::ModelState) -> Self::ObservableState;
}
```

**Case study: evmap.** The `evmap` crate is a lock-free, eventually consistent concurrent map. Writers update one copy while readers see the other; writes become visible only after `refresh()`. Standard lockstep would fail because reads return stale data by design. With the eventual consistency extension, the framework runs operations without per-step bridge checks, then calls `refresh()` (the sync operation) and verifies convergence. The test passes, correctly characterizing evmap's consistency model.

```rust
fn sut_sync(sut: &mut EvmapStore) -> HashMap<String, String> {
    sut.refresh();
    sut.snapshot()
}
fn model_sync(state: &EvmapModel) -> HashMap<String, String> {
    state.data.clone()
}
```

### 5.4 Session Consistency Testing

The `SessionConsistencyModel` extension checks per-session ordering guarantees: read-your-writes (if session A writes X, its next read sees X) and monotonic reads (a session's reads never go backward). These sit between linearizability (too strong for many systems) and eventual consistency (too weak for client-facing APIs).

The trait requires the user to identify sessions, keys, and observations:

```rust
pub trait SessionConsistencyModel: InvariantModel {
    type SessionId: Debug + Clone + Eq + Hash + 'static;
    type Key: Debug + Clone + Eq + Hash + 'static;
    type Observation: Debug + Clone + PartialEq + 'static;
    fn session_of(action: &dyn AnyAction) -> Option<Self::SessionId>;
    fn read_observation(action: &dyn AnyAction, result: &dyn Any)
        -> Option<(Self::Key, Self::Observation)>;
    fn write_observation(action: &dyn AnyAction)
        -> Option<(Self::Key, Self::Observation)>;
}
```

**Case study: Multi-session KV store.** The session KV example tests a store with three sessions (`0`, `1`, `2`). Each `Put` and `Get` is tagged with a session ID. The framework tracks per-session write histories and read observations, verifying that each session sees its own writes and that reads are monotonic.

## 6. Advanced Features

proptest-lockstep includes six additional features that, taken together, distinguish it from all prior lockstep testing frameworks.

### 6.1 Effect-Indexed Commutativity

The DPOR commutativity check (Section 4.2) runs the model twice per operation pair --- an O(n^2) cost. For data structures with many operations, this becomes expensive. The `EffectModel` and `ConflictAlgebra` traits allow users to annotate actions with *effects* --- read/write footprints keyed by resource --- and determine commutativity in O(1) by checking effect conflict.

```rust
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ReadWriteEffect<K> {
    Read(K), Write(K), ReadAll, WriteAll, None,
}
```

Two actions commute iff their effects do not conflict: Read/Read always commutes; Read/Write conflicts on the same key; Write/Write conflicts on the same key. The dynamic model oracle remains as a fallback for unannotated actions. The soundness is proved in `EffectLattice.lean`: `effect_sound` establishes that non-conflict implies model commutativity, and `effect_dpor_sound` chains this to DPOR soundness.

### 6.2 Bisimulation-Guided Shrinking

When a test fails, proptest's generic shrinking produces non-minimal counterexamples because it does not understand the lockstep structure. The `shrinking` module performs a post-hoc minimization pass that exploits the bisimulation:

1. **Find the failure depth** --- the first step where `check_bridge` fails.
2. **Remove prefix actions** --- try removing each action before the failure point. If the failure still occurs at the same or earlier depth, the action was irrelevant.
3. **Return the minimal sub-trace** --- the shortest sequence that triggers the bug.

This is based on the `bug_localization` theorem: if `bounded_bisim` fails at depth n+1, some specific action witnesses the failure. The bisimulation's monotonicity guarantees that removing irrelevant actions can only surface the failure earlier.

The verbose runner `run_lockstep_test_verbose` automatically applies this minimization on failure, printing the minimal counterexample to stderr before panicking.

### 6.3 Model-Coverage-Guided Generation

The `CoverageGuidedModel` extension uses the model's reachable state space as a semantic coverage map. Instead of random-with-preconditions generation, it scores candidate actions by whether they lead to *novel model states*:

```rust
pub trait CoverageGuidedModel: LockstepModel {
    fn coverage_key(state: &Self::ModelState) -> u64;
}
```

At each step, the runner generates N candidate actions (default: 10), forward-simulates each through a clone of the model (cheap: pure data), and selects the one that lands in the most novel coverage bucket. Good coverage keys capture the "shape" of the state: for a KV store, `(num_keys, has_duplicates, max_value_len)`; for a cache, `(occupancy_ratio, num_evictions)`.

This is a novel combination: the model that already exists for lockstep testing doubles as the coverage oracle. No separate instrumentation is required.

### 6.4 Compositional Testing

The `compositional` module enables modular testing of composed systems. Two independent lockstep models (subsystem A and subsystem B) are tested separately, and the `verify_composition` function confirms that both pass. The `product_bisim_iff` theorem (proved in `Compositional.lean`) guarantees that the product satisfies bounded bisimulation iff both components do.

The `IncrementalComposition` tracker adds efficiency: when one subsystem's implementation changes, only that subsystem needs re-testing. The other subsystem's previous result carries over. Bridge precision is tracked per subsystem via the `BridgePrecision` enum (`Opaque`, `Mixed`, `Transparent`); upgrading to a finer precision invalidates the subsystem (by `refines_strengthen_bisim`: finer bridges are strictly stronger), while downgrading reuses the stronger result.

### 6.5 Differential Bridge Testing

The `DifferentialBridgeModel` extension is a meta-testing technique: it tests the test oracles themselves. Given two bridges for the same action --- the user's (potentially coarse) and a stricter one --- the framework runs both and reports when the coarse bridge passes but the strict bridge fails. This detects overly-coarse `Opaque` bridges that should be `Transparent`, catching hidden bugs that the user's test would miss.

### 6.6 Runtime Refinement Contracts

The `RefinementGuard` turns the bridge algebra into a runtime contract system. The model runs as a shadow alongside the SUT, and bridge checks are performed at every operation boundary. Violations are recorded (not panicked on), enabling use in staging, canary deployments, and integration tests. The same bridge algebra that powers lockstep testing also powers runtime verification. Performance tracking measures model execution and bridge check overhead per operation, and a configurable sampling rate reduces overhead for production-adjacent environments.

## 7. Case Studies

We applied proptest-lockstep to six real-world Rust crates and an intentional bug-detection suite. This section reports the results.

### 7.1 Crossbeam Queue

**Crate:** `crossbeam-queue` (approximately 50 million downloads). **Data structures tested:** `ArrayQueue` (bounded lock-free MPMC queue) and `SegQueue` (unbounded lock-free MPMC queue). **Model:** `VecDeque<i32>` with capacity tracking for `ArrayQueue`. **Actions:** `push`, `force_push`, `pop`, `len`, `is_empty`, `is_full`. **Bridges:** All auto-derived --- `ResultBridge<Transparent<()>, Transparent<i32>>` for `push`, `OptionBridge<Transparent<i32>>` for `pop` and `force_push`, `Transparent<usize>` for `len`, `Transparent<bool>` for `is_empty` and `is_full`. **Features exercised:** Sequential lockstep, concurrent linearizability with DPOR. **Result:** All tests pass. No bugs found. 100 Shuttle schedules with 2 branches of 5 operations each, linearizability confirmed for all.

### 7.2 evmap

**Crate:** `evmap` (eventually consistent concurrent map). **Model:** `HashMap<String, String>`. **Actions:** `insert`, `get`, `contains_key`, `refresh`. **Features exercised:** Eventual consistency testing. Standard lockstep fails by design (reads return stale data). After `refresh()`, all observations converge. **Result:** All eventual consistency tests pass. This demonstrates the framework correctly handles a real EC crate.

### 7.3 DashMap

**Crate:** `dashmap` (approximately 30 million downloads, sharded concurrent hash map). **Model:** `HashMap<String, i32>`. **Actions:** `insert`, `get`, `remove`, `contains_key`, `len`, `or_insert`, `alter`. **Bridges:** All auto-derived. **Features exercised:** Sequential lockstep, concurrent linearizability. **Result:** All tests pass under both sequential and concurrent modes.

### 7.4 scc::HashMap

**Crate:** `scc` (scalable concurrent collections with epoch-based reclamation). **Model:** `HashMap<String, String>`. **Actions:** `insert`, `upsert`, `remove`, `get`, `contains_key`, `len`. **Features exercised:** Sequential lockstep, concurrent linearizability. **Result:** All tests pass.

### 7.5 Treiber Stack

**Implementation:** Hand-written lock-free stack using `AtomicPtr` and CAS. **Model:** `Vec<i32>`. **Actions:** `push`, `pop`, `is_empty`. **Features exercised:** Sequential lockstep, concurrent linearizability, ConflictMaximizing scheduling. **Result:** All tests pass. The CAS-based implementation is linearizable under all explored schedules.

### 7.6 Intentional Bug Detection

The `bug_detection` example contains four intentionally buggy implementations:

| Bug | Description | Detected by | Min. trace length |
|-----|------------|------------|------------------|
| Off-by-one pop | Stack returns second element instead of top | `Transparent<Option<i32>>` bridge | 3 (push, push, pop) |
| Stale cached length | Queue `len()` uses non-atomic cached counter | `Transparent<usize>` bridge | 4 (enqueue, dequeue, dequeue, len) |
| Lost CAS update | Counter loses increments under retry | `Transparent<u64>` bridge | 2 (increment, get) |
| Wrong LRU eviction | Cache evicts MRU instead of LRU | `OptionBridge<Transparent<String>>` bridge | capacity+1 inserts |

Each test uses `#[should_panic]` to confirm the framework catches the bug. All four are detected via bridge mismatch within the first few proptest cases. The bisimulation-guided shrinking module reduces counterexamples to minimal traces.

### 7.7 Summary Table

| Case study | Lines of test code | Bridges (manual/auto) | Features exercised | Result |
|-----------|-------------------|----------------------|-------------------|--------|
| crossbeam-queue | 180 | 0 / 6 | sequential, linearizability | Pass |
| evmap | 150 | 0 / 4 | eventual consistency | Pass |
| dashmap | 160 | 0 / 7 | sequential, linearizability | Pass |
| scc::HashMap | 140 | 0 / 6 | sequential, linearizability | Pass |
| Treiber stack | 130 | 0 / 3 | sequential, linearizability, ConflictMax | Pass |
| Bug detection | 300 | 0 / 8 | sequential, shrinking | 4 bugs caught |

The zero manual bridges column reflects the polynomial bridge derivation: all bridges were auto-derived from type annotations. Total test code across all case studies is under 1100 lines.

## 8. Formal Metatheory

The metatheory of proptest-lockstep is machine-checked in Lean 4. The formalization spans 29 files containing over 300 definitions and theorems with zero uses of `sorry`. To our knowledge, no other property-based testing framework has formal proofs of its core methodology.

### 8.1 Core Theorems

The formalization proves four central results:

**Runner correspondence (biconditional).** The theorem `runner_bounded_bisim_equiv` in `Runner.lean` establishes that the runner's operational bridge checks are *exactly* the obligations of bounded bisimulation:

```
(forall traces of length n, runner_passes trace sm ss) <-> bounded_bisim n sm ss
```

The forward direction is the soundness result: passing tests imply bisimulation. The reverse direction confirms completeness: bisimulation implies the runner would pass.

**DPOR soundness.** The theorem `dpor_swap_sound` in `DPOR.lean` proves that swapping two adjacent commuting operations in a linearization preserves validity. The biconditional `dpor_swap_iff` confirms that commuting operations are fully interchangeable. This extends to arbitrary positions via `dpor_swap_at`.

**Crash-recovery soundness.** The theorem `crash_bisim_implies_bounded` in `CrashRecovery.lean` proves that crash bisimulation is strictly stronger than normal bounded bisimulation. The theorem `crash_bisim_double_crash` proves that the system survives multiple consecutive crashes. The theorem `crash_recovery_preserves` establishes that recovered states remain in the bisimulation.

**Compositional testing (biconditional).** The theorem `product_bisim_iff` in `Compositional.lean` proves that the product of two systems satisfies bounded bisimulation iff both components do. This justifies testing subsystems independently and composing the guarantees.

### 8.2 Bridge Algebra Proofs

The bridge algebra is formalized as a logical relation (Reynolds, 1983). Each lift preserves bridge equivalence: `sum_preserves_ok`, `prod_preserves`, `option_preserves_some`, `list_preserves_cons`. Bridge equivalence is decidable (`bridge_equiv_decidable`), connecting the Lean `Prop`-level proofs to the Rust `check_bridge` function.

The refinement preorder on bridges (`BridgeRefinement.lean`) proves that opaque is the coarsest bridge, transparent is the finest, and all lifts are monotone: finer components produce finer composite bridges. The key theorem `refines_strengthen_bisim` establishes that replacing bridges with finer ones preserves bounded bisimulation.

The polynomial bridge derivation is proved monotone in `DerivedBridge.lean` and `PolynomialBridge.lean`: each derivation step preserves the refinement ordering.

### 8.3 Additional Formalizations

Beyond the core, the formalization covers: observational refinement (biconditional with bounded bisimulation, `ObservationalRefinement.lean`), testing completeness (any observable discrepancy is detected at sufficient depth, `TestingCompleteness.lean`), opaque handle detection (wrong handles are detected when used, `OpaqueDetection.lean`), precondition filtering (`Precondition.lean`), effect-indexed commutativity (`EffectLattice.lean`), session consistency (`SessionConsistency.lean`), eventual consistency (`EventualConsistency.lean`), certified bridge synthesis (`CertifiedSynthesis.lean`), projection chains (`Projection.lean`), environment threading (`Environment.lean`), and certificate hash verification (`CertificateHash.lean`).

### 8.4 The Rust-Lean Gap

The formalization is a *specification verification*: Lean proves properties of abstract definitions that are designed to mirror the Rust implementation. It is not a code verification --- no Lean theorem directly constrains the Rust code. The gap is bridged by shared structure: `runner_passes` in Lean mirrors `LockstepSut::apply` in Rust; `bridge_equiv` in Lean mirrors `LockstepBridge::check`; `CertificateHash.lean` cross-verifies FNV-1a hash values between Lean and Rust.

Specific gaps: Lean's `runner_passes` quantifies over *all* traces, while the Rust runner *samples* via proptest (probabilistic, not absolute coverage). Lean requires `DecidableEq` on observed types, while Rust requires `PartialEq`. The proc macro's code generation is not itself verified. These gaps are intentional and documented: formalizing Rust semantics in Lean would require embedding Rust's type system (cf. RustBelt), which is a separate research project.

## 9. Related Work

**quickcheck-lockstep** (de Vries, 2021) is the direct predecessor. It introduced the lockstep pattern for Haskell's QuickCheck, with GADT-based action types, opaque variable tracking, and observational refinement. proptest-lockstep adapts the core ideas to Rust's type system, replacing Haskell's GADTs with `Is<A,B>` witnesses and the `Phase` GAT, and extends the framework with concurrent linearizability testing, crash-recovery, session consistency, eventual consistency, effect-indexed commutativity, compositional testing, and machine-checked formal proofs --- none of which are present in quickcheck-lockstep. The polynomial bridge derivation via proc macro has no counterpart in the Haskell library, where bridges are written manually.

**proptest-state-machine** (Joyent, 2022) provides the foundation that proptest-lockstep builds on: a `ReferenceStateMachine` / `StateMachineTest` split for proptest. It lacks bridges (model and SUT return values are not compared structurally), opaque handle tracking, concurrent linearizability testing, and all extension traits. proptest-lockstep wraps proptest-state-machine, adding the bridge algebra, proc macro, and extension hierarchy.

**Jepsen** (Kingsbury, 2013--present) is the most widely used tool for testing distributed systems. It is empirical: black-box fault injection against real deployments, with correctness checked by post-hoc analysis of operation histories. Jepsen has no model (no lockstep comparison), no formal backing, and operates at the distributed-system level rather than the data-structure level. proptest-lockstep complements Jepsen: it tests individual components in-process with a formal model, while Jepsen tests assembled systems under real network failures.

**Perennial** (Chajed et al., 2019) provides full Coq verification of crash-safe storage systems. It proves functional correctness, not just testing-time agreement. The verification effort is orders of magnitude larger than writing a lockstep model: Perennial's FSCQ verification required approximately 30,000 lines of Coq. proptest-lockstep occupies a practical middle ground --- a model of 50 lines plus machine-checked metatheory gives high confidence without full verification.

**Stateright** (Nadal, 2021) is a Rust model checker that explores model state spaces exhaustively. It operates on *models only* --- it does not run real code. proptest-lockstep tests *real implementations* against models. The two approaches are complementary: Stateright verifies model properties; proptest-lockstep verifies that implementations match models.

**Shuttle** (Amazon, 2021) is a randomized concurrency testing framework for Rust that explores thread schedules. proptest-lockstep uses Shuttle as the schedule exploration engine in its concurrent testing pipeline, adding the model, linearizability checking, DPOR, and ConflictMaximizing scheduling on top.

**loom** (Tokio, 2019) provides exhaustive schedule enumeration for Rust concurrency testing. proptest-lockstep integrates with loom via the `concurrent-loom` feature flag, providing exhaustive small-state-space verification as an alternative to Shuttle's randomized approach.

**QuickCheck / Hedgehog / Hypothesis.** General-purpose PBT frameworks that support stateful testing but lack lockstep-specific features: no bridge algebra, no opaque handle tracking, no concurrent linearizability, no formal metatheory.

In summary, proptest-lockstep occupies a unique point in the design space: it combines the lockstep methodology of quickcheck-lockstep, the Rust integration of proptest-state-machine, the concurrent testing of Shuttle/loom, and the formal rigor of Perennial, while being practical enough that a 50-line model and a `#[lockstep_actions]` annotation suffice to test a real crate.

## 10. Conclusion

We have presented proptest-lockstep, a Rust library for lockstep-style stateful property-based testing. The tool provides a proc macro that derives bridges from type structure, eliminating 80--90% of the boilerplate that makes stateful PBT impractical. It extends the core lockstep methodology with concurrent linearizability testing (DPOR, sleep sets, ConflictMaximizing scheduling), crash-recovery testing, eventual and session consistency testing, effect-indexed commutativity, bisimulation-guided shrinking, model-coverage-guided generation, compositional testing, differential bridge testing, and runtime refinement contracts.

We have applied the framework to six real-world Rust crates --- crossbeam-queue, evmap, dashmap, scc, a hand-written Treiber stack, and an intentional bug suite --- confirming correctness under thousands of generated sequences and schedules, and detecting four classes of bugs in intentionally faulty implementations.

The metatheory is machine-checked in Lean 4: 29 files, over 300 definitions and theorems, zero `sorry`. The formalization proves that lockstep testing is sound (runner agreement is a biconditional with bounded bisimulation), that DPOR schedule reordering preserves observable behavior, that crash-recovery testing correctly characterizes crash bisimulation, and that compositional testing is a biconditional. No other property-based testing framework has formal proofs of its core methodology.

proptest-lockstep is open-source and available at `https://github.com/joshburgess/proptest-lockstep`. All 27 examples are self-contained and run with `cargo test`. The library requires only the standard Rust toolchain; the Lean formalization requires `lake build` in the `formal_verification/` directory.

**Future work.** Three directions are planned. First, integration with `cargo-fuzz` for hybrid fuzzing: coverage-guided fuzzing generates interesting byte streams, which are decoded into lockstep action sequences, combining the exploration power of fuzzing with the semantic checking of lockstep. Second, IDE support for bridge error diagnostics: when a bridge type mismatch occurs, the proc macro could emit structured diagnostics pointing to the specific type component that failed to bridge. Third, scaling DPOR to larger thread counts: the current ConflictMaximizing strategy is an approximation; a tighter integration with Shuttle's scheduler could enable targeted exploration of specific conflict patterns identified by the effect algebra.
