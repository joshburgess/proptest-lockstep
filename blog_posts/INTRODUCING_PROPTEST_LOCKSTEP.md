# GATs, Type Witnesses, and the Art of Stateful Testing

*How I built `proptest-lockstep` — and what Rust's type system is really capable of*

---

If you've ever tested a stateful system — a database, a file system, a caching layer, a concurrent data structure — you know the feeling. You write a few unit tests. They pass. You ship. And then production finds the seven-step sequence of API calls that puts your system into a state you never imagined.

Property-based testing helps. Instead of handcrafting test cases, you generate thousands of random inputs and check that invariants hold. Libraries like `proptest` have made this accessible to every Rust programmer. But stateful systems present a harder problem: you don't just need random *values*, you need random *sequences of operations*, where each operation might depend on the result of a previous one. And when something fails, you need the framework to shrink that 200-step sequence down to the 3 steps that actually matter.

`proptest-lockstep` is a new crate that solves this problem using a technique called *lockstep testing*. The technique was developed by Edsko de Vries at Well-Typed and embodied in Haskell's `quickcheck-lockstep` — a library used in Well-Typed's consulting and training work for testing stateful systems.

Bringing it to Rust wasn't a straightforward translation. It required solving several type system problems that many people assume Rust simply can't handle. The solutions turned out to be interesting in their own right — a practical showcase for GATs, type equality witnesses, and composable trait algebras that goes well beyond testing.

This post is about the ideas that make it work.

---

## The Idea: Your Model Is Always Right

Lockstep testing starts with a simple premise: if you can write a *pure model* of your system, you can test the real system by running both in lockstep and comparing their outputs at every step.

Say you're testing a file system API. You write a simple in-memory mock — a `HashMap<String, String>` for files, a counter for generating mock handles. Then:

1. Generate a random sequence of operations: `Open`, `Write`, `Close`, `Read`.
2. Execute each operation against the real file system *and* the mock.
3. After every step, check: did they return the same thing?

If the real system returns `Err(AlreadyExists)` but the model returns `Err(DoesNotExist)`, you've found a bug. If they both return `Ok(())`, move on.

This is powerful because the model is trivially correct (it's a `HashMap`) and the property is trivially stated ("they agree"). All the intelligence is in the *generation* — producing interesting sequences that exercise edge cases — and in the *shrinking* — reducing a failing 50-step sequence to the minimal 2 or 3 steps that reproduce the bug.

But there's a catch. When you open a file, the real system returns a `FileHandle` — an opaque descriptor. The model can't return a real file handle. It returns a `MockHandle`. You can't compare these directly. And yet, if the real system gives you the *wrong* handle, you need to notice eventually.

This is the problem of *observability*, and it's at the heart of everything that follows.

---

## Observability, or: Not Everything Is Comparable

Some types are *transparent*: a `String` from the model is the same as a `String` from the real system, and you can compare them with `==`. Some types are *opaque*: a `FileHandle` and a `MockHandle` are fundamentally different types, and comparing them is meaningless. If the system returns the wrong handle, you'll only notice later, when you *use* that handle and get the wrong file contents.

In the Haskell original, this is handled with two GADTs — `ModelValue` and `Observable` — that the user defines manually for every type shape in their API. For a file system with five return types, that's ten GADT constructors plus two interpretation functions. It works, but it's a lot of boilerplate, and the structure is repetitive: the `Result` case always wraps two sub-cases, the tuple case always wraps two sub-cases, and so on.

What if observability were *composable*?

### The Bridge Algebra

In `proptest-lockstep`, you never write GADT constructors. Instead, you describe the relationship between real and model types using a small algebra of *bridges*:

```rust
pub trait LockstepBridge {
    type Real;
    type Model;
    type Observed: Debug + PartialEq;
    fn observe_real(r: &Self::Real) -> Self::Observed;
    fn observe_model(m: &Self::Model) -> Self::Observed;
}
```

A bridge says: "here's how to project a real value and a model value into a common *observed* form that can be compared."

Two primitive bridges cover the most common cases:

- `Transparent<T>` — the model and real types are the same, and directly comparable. `type Observed = T`.
- `Opaque<R, M>` — the types differ, and comparison is meaningless. `type Observed = ()`.

And then bridges compose over type constructors:

```rust
ResultBridge<OkB, ErrB>   // bridges for Ok and Err cases
TupleBridge<AB, BB>       // bridges for each tuple element
OptionBridge<B>           // bridge for the inner type
VecBridge<B>              // bridge for each element
```

The bridge for `Result<(FileHandle, String), FsErr>` vs `Result<(MockHandle, String), FsErr>` is:

```rust
ResultBridge<
    TupleBridge<Opaque<FileHandle, MockHandle>, Transparent<String>>,
    Transparent<FsErr>,
>
```

Read it inside-out: the `Ok` case is a tuple where the first element is opaque (handles) and the second is transparent (paths); the `Err` case is transparent (error codes). The compiler verifies that this bridge actually connects the right pair of types — get it wrong, and you get a type error, not a runtime surprise.

This is one of those designs that feels inevitable in retrospect but took a while to arrive at. The key insight is that observability has the same algebraic structure as the types it describes: if `Result<A, B>` is built from `A` and `B`, then the bridge for `Result<A, B>` is built from the bridges for `A` and `B`. We're just lifting the type algebra into a trait algebra.

---

## The Phase Problem: Symbolic and Concrete

Here's a subtler issue. When we *generate* a test sequence, the operations don't have real values yet. If step 3 is "write to the handle you got from step 1," we need a placeholder — a *symbolic variable* — that stands in for the handle we haven't created yet. During *execution*, those placeholders are replaced with real values.

Hedgehog, the Haskell property testing library, handles this elegantly by parameterising everything by a type constructor `v :: Type → Type`, which is `Symbolic` during generation and `Concrete` during execution. The state type becomes `State v`, and a handle reference becomes `Var FileHandle v` — a symbolic token during generation, a real handle during execution.

This requires higher-kinded types, which Rust doesn't have. For years, this was considered a fundamental limitation. But Rust 1.65 stabilized Generic Associated Types, and it turns out that GATs are sufficient.

```rust
pub trait Phase: Clone + Debug + 'static {
    type Var<T: 'static>;
}

pub struct Symbolic;
impl Phase for Symbolic {
    type Var<T: 'static> = SymVar<T>;  // opaque token: just a usize + PhantomData
}

pub struct Concrete;
impl Phase for Concrete {
    type Var<T: 'static> = ConVar<T>;  // real value wrapper
}
```

A note on the GAT bounds: you might expect `type Var<T: 'static>: Clone + Debug`, but in practice the GAT can't carry those bounds without requiring them on `T` for all `Phase` implementations. `ConVar<T>` implements `Clone` and `Debug` only when `T` does, and the GAT must be satisfied for *all* `T: 'static`. So the bounds live on the downstream usage sites rather than on the GAT definition — a minor Rust pragmatism.

In practice, `proptest-lockstep` uses the symbolic phase directly: action structs contain `SymVar<T>` fields (via `GVar`) during generation, and the framework resolves them to concrete values during execution using a `TypedEnv` — a heterogeneous variable environment keyed by ID and type. You don't parameterize your state type by `Phase` yourself; the framework handles the symbolic-to-concrete transition internally.

The conceptual split is the same as Hedgehog's — symbolic variables during generation, real values during execution — but the mechanism is different. Instead of parameterizing everything by a type constructor, the phase distinction lives in the `GVar` type and the `TypedEnv` resolution. `SymVar` is just a `usize` with a phantom type; resolution happens by looking up the ID in the environment and applying a projection chain. Zero boxing, zero dynamic dispatch for the phase transition itself.

---

## The Exhaustiveness Problem: Simulating GADTs

This is where things get really interesting.

In Haskell, all actions live in a single GADT:

```haskell
data Action a where
  Open  :: Path -> Action (Result (Handle, Path) Err)
  Write :: Var Handle -> String -> Action (Result () Err)
  Read  :: Path -> Action (Result String Err)
```

Each constructor pins the type parameter `a` to that action's return type, and `case` analysis on this GADT is *exhaustive* — forget a constructor, and the compiler rejects your code.

This gives you two things at once: you can't forget to handle an action, and within each branch, the compiler knows the return type. The model interpreter for `Open` can return a `Result<(MockHandle, Path), Err>`, and the compiler verifies that's correct for that branch.

Rust doesn't have GADTs. My first design used separate structs per action (`OpenAction`, `WriteAction`, ...), each implementing a trait, collected via `Box<dyn DynAction>`. This preserved the typed returns but lost exhaustiveness — nothing stopped you from forgetting to handle a case.

I spent a long time on this problem. There were pragmatic solutions (proc macros that generate an enum wrapper, `enum_dispatch`), but I wanted the real thing: compile-time exhaustiveness *and* per-arm type refinement. And it turns out Rust can do it.

### Type Equality Witnesses

The key is a type called `Is<A, B>`:

```rust
pub struct Is<A, B>(PhantomData<fn(A) -> B>);

impl<A> Is<A, A> {
    pub fn refl() -> Self { Is(PhantomData) }
}
```

`Is<A, B>` is a *proof that A and B are the same type*. The only way to construct one is `Is::refl()`, which requires `A == B` — the compiler enforces this. If you have an `Is<A, B>` in hand, you know with certainty that `A` and `B` are the same type, and you can safely cast between them.

This is a well-known technique in the type theory literature (it's closely related to Leibniz equality), and it's been used in Haskell and OCaml for years. But it works in Rust too, and it lets us build GADT-like enums.

### The GADT Enum

Each variant of our action enum carries an `Is<>` witness that constrains the return type parameter:

```rust
pub enum FsGadt<R> {
    Open(Is<Result<(FileHandle, String), FsErr>, R>, Open),
    Write(Is<Result<(), FsErr>, R>, Write),
    Close(Is<Result<(), FsErr>, R>, Close),
    Read(Is<Result<String, FsErr>, R>, Read),
}
```

`FsGadt::Open(Is::refl(), open_data)` only compiles when `R = Result<(FileHandle, String), FsErr>`, because `Is::refl()` requires the two type arguments to be identical.

Now, `match` on `FsGadt<R>` is exhaustive — add a variant and forget to handle it, and the compiler rejects your code. And within each arm, the `Is<>` witness tells you exactly what `R` is, so you can return a correctly-typed value.

The proc macro generates a typed `run_sut` method on the GADT that uses the witness for casting:

```rust
impl<R> FsGadt<R> {
    pub fn run_sut<I: FsSutInterp>(&self, sut: &mut I::Sut, env: &TypedEnv) -> R {
        match self {
            FsGadt::Open(proof, action) => {
                let result: Result<(FileHandle, String), FsErr> =
                    I::open(sut, action, env);
                proof.cast(result) // safe: proof witnesses R = this type
            }
            FsGadt::Write(proof, action) => {
                let result: Result<(), FsErr> =
                    I::write(sut, action, env);
                proof.cast(result)
            }
            // ... exhaustive — compiler enforces all arms present
        }
    }
}
```

The `proof.cast()` call is where the `Is<>` witness earns its keep. It converts the concrete `Result<(FileHandle, String), FsErr>` to the generic `R`, which the type system now knows is the same type. The single `unsafe` pointer cast inside `cast()` (using `ManuallyDrop` + `ptr::read` to avoid double-drop) is encapsulated in the library and sound by construction — the witness can only exist when the types are equal.

There's a subtlety here. The GADT is parameterized by the SUT's return type (`real_return`), so the witness works directly for the SUT interpreter. For the model interpreter, the return type may differ — `Open` returns `Result<(MockHandle, String), FsErr>` on the model side, not `Result<(FileHandle, String), FsErr>`. The model dispatch goes through a different path: the proc macro generates typed interpreter traits, and a `dispatch_model` helper boxes the typed result into `Box<dyn Any>`. The witness isn't needed there because the types are concrete, not generic. It's a pragmatic split: witnesses where they work (SUT), dynamic dispatch where they don't (model with opaque types).

Users never write the GADT enum or `run_sut` themselves. A proc macro generates everything from annotated action structs. Users write:

```rust
#[lockstep_actions(state = MockFs)]
pub mod fs {
    #[action(
        real_return = "Result<(FileHandle, String), FsErr>",
        model_return = "Result<(MockHandle, String), FsErr>",
        bridge = "ResultBridge<TupleBridge<Opaque<FileHandle, MockHandle>, Transparent<String>>, Transparent<FsErr>>",
    )]
    pub struct Open { pub path: String }

    #[action(
        real_return = "Result<(), FsErr>",
        bridge = "ResultBridge<Transparent<()>, Transparent<FsErr>>",
        uses = [handle],
    )]
    pub struct Write {
        pub handle: GVar<OpenReal, FileHandle, HandleProj>,
        pub data: String,
    }

    // ...
}
```

Each action declares its `real_return` type (what the SUT returns) and its `bridge` (how to compare SUT and model results). When the model returns the same type as the SUT — the common case for transparent types — `model_return` can be omitted entirely. When the types differ (opaque handles), `model_return` is specified explicitly.

The bridge types use short names (`Transparent`, `ResultBridge`, etc.) because the proc macro auto-imports the prelude into the generated module.

From these annotations, the macro generates the GADT enum, the visitor trait, the `Is<>` witnesses, the bridge dispatch, the variable storage, typed interpreter traits, and dispatch helpers. Users get exhaustive matching, typed returns, bridge verification, and variable tracking — all at compile time.

### The Visitor Trait

The proc macro also generates a visitor trait — one method per action variant. Any code that processes actions must implement the full visitor, which enforces exhaustiveness at the *consumer* site too:

```rust
pub trait FsVisitor {
    type Output;
    fn visit_open(&mut self, action: &Open) -> Self::Output;
    fn visit_write(&mut self, action: &Write) -> Self::Output;
    fn visit_close(&mut self, action: &Close) -> Self::Output;
    fn visit_read(&mut self, action: &Read) -> Self::Output;
}
```

Forget to add `visit_read`? Compile error. Add a new `Seek` action and forget to update the visitor? Compile error. This is exhaustiveness enforcement at every point in the system that processes actions, not just the `match` on the enum.

### Typed Interpreter Traits

For the model and SUT interpreters, the macro generates typed traits with one method per action. In user-written code, there's no `Box<dyn Any>`, no downcasting, no match boilerplate — the framework handles the boxing at the boundary:

```rust
pub trait FsModelInterp {
    type State;
    fn open(state: &mut Self::State, action: &Open, env: &TypedEnv) -> OpenModel;
    fn write(state: &mut Self::State, action: &Write, env: &TypedEnv) -> Result<(), FsErr>;
    fn close(state: &mut Self::State, action: &Close, env: &TypedEnv) -> Result<(), FsErr>;
    fn read(state: &mut Self::State, action: &Read, env: &TypedEnv) -> Result<String, FsErr>;
}
```

Each method returns the action's declared return type directly. The framework handles the boxing and unboxing at the boundary. The user implements the interpreter by writing the natural code for each operation:

```rust
impl fs::FsSutInterp for FsLockstep {
    type Sut = RealFs;

    fn open(sut: &mut RealFs, a: &fs::Open, _: &TypedEnv) -> OpenReal {
        sut.open(&a.path)
    }

    fn write(sut: &mut RealFs, a: &fs::Write, env: &TypedEnv) -> Result<(), FsErr> {
        match resolve_gvar(&a.handle, env) {
            Some(h) => sut.write(&h, &a.data),
            None => Err(FsErr::BadHandle),
        }
    }

    // ...
}
```

---

## Variable Projections: A Small Language for Decomposition

There's one more piece worth understanding, because it solves a problem that trips up everyone who writes stateful property tests.

When `Open` returns `Result<(FileHandle, String), FsErr>`, the test framework stores this as a single variable. But `Write` needs just the `FileHandle`. You need to *project* — to extract a component from a compound result.

In Edsko's original library, this is handled by a small DSL called `Op` — essentially a tiny, inspectable language for describing projections. I adapted this for Rust's trait system, with one key difference: projections return `Option<B>` rather than being total, so `OpOk` on an `Err` value returns `None` instead of panicking:

```rust
pub trait Op<A, B>: Debug + Clone + Send + Sync + 'static {
    fn apply(&self, a: &A) -> Option<B>;
}

pub struct OpOk;   // Result<T, E> → T
pub struct OpFst;  // (A, B) → A
pub struct OpComp<F, G, Mid> { /* fields private — use OpComp::new(f, g) */ }
```

A `GVar<X, Y, O>` ties a symbolic variable of type `X` to a projection `O: Op<X, Y>`:

```rust
let open_result: SymVar<Result<(FileHandle, String), FsErr>> = /* from Open */;
let handle = GVar::new(open_result, OpOk).then(OpFst);
// Type: GVar<Result<(FileHandle, String), FsErr>, FileHandle, OpComp<OpOk, OpFst, (FileHandle, String)>>
```

`OpComp` has three type parameters — the two operations plus the intermediate type that connects them. In Haskell, the intermediate type can be inferred and hidden. Rust needs it explicit for type inference. In practice, users define a type alias — `type HandleProj = OpComp<OpOk, OpFst, (FileHandle, String)>` — and never think about it again.

Every link in the chain is checked at compile time. `OpOk` only applies to `Result`. `OpFst` only applies to tuples. `OpComp` only type-checks when the intermediate types align. If you try to project `OpFst` out of a `Result` (instead of applying `OpOk` first), the compiler catches it.

This is one of those cases where Rust's trait system gives us something very close to a dependently-typed language. The projection chain is a *program* written in a small type-level language, and the compiler is its interpreter.

### Model-Side Resolution

There's an asymmetry when opaque handles are involved. The SUT side resolves a `GVar<OpenReal, FileHandle, HandleProj>` directly — the `TypedEnv` stores `OpenReal` values, and `resolve_gvar` applies the projection chain. But the model side stores `OpenModel` (with `MockHandle`, not `FileHandle`), so the same `GVar` can't be used to look up the model environment.

The library provides `resolve_model_gvar` for this case — you specify the model type and a model-side projection chain:

```rust
fn write(s: &mut MockFs, a: &fs::Write, env: &TypedEnv) -> Result<(), FsErr> {
    match resolve_model_gvar::<OpenModel, MockHandle, ModelHandleProj>(
        a.handle.var_id(),
        &OpComp::new(OpOk, OpFst),
        env,
    ) {
        Some(h) => s.write(&h, &a.data),
        None => Err(FsErr::BadHandle),
    }
}
```

The SUT interpreter uses `resolve_gvar(&a.handle, env)` — the `GVar` carries everything it needs. The model interpreter uses `resolve_model_gvar` with the model type explicitly. This mirrors the fundamental asymmetry: the `GVar` is typed against the real return type (because it's used in action structs during generation), but the model environment stores the model return type (because the model produces different values for opaque handles).

---

## How the Runner Works

The lockstep comparison happens in a self-contained runner that avoids shared mutable state between the reference (model) side and the SUT side.

The `LockstepSut` — the SUT side of the test — maintains its own independent copy of the model state and environment. On each step, it re-runs the model against its own copy, runs the SUT, and compares the results through the bridge. This means the model executes twice per step: once on the reference side (for state advancement and proptest's shrinking) and once on the SUT side (for the lockstep comparison).

This is a deliberate trade-off. The alternative — sharing the model result between the reference and SUT sides via shared mutable state — would introduce a temporal coupling that could silently produce wrong results during shrinking, when `proptest-state-machine` replays action prefixes. Since models are cheap, pure data structures (they're `HashMap`s and counters, not databases), the doubled execution is a trivial cost for architectural soundness.

---

## What Proptest Users Get

If you're already using `proptest` or `proptest-state-machine`, here's what `proptest-lockstep` adds:

**You never write a shrinker.** The Haskell original requires a manual `shrinkWithVars` function. Forget it, and counterexamples are unreduced and incomprehensible. With proptest, shrinking is integrated — both the sequence length and individual action arguments shrink automatically.

**The postcondition is always the same.** You don't write ad-hoc assertions per action. The lockstep property — "model and system agree, up to observability" — is universal and generated from the bridge annotations. One property tests everything.

**Variable management is automatic.** The framework tracks which actions produce variables, which actions consume them, and ensures that preconditions are maintained during shrinking. If the shrinker removes an `Open` action, all dependent `Write` and `Close` actions are automatically removed too.

**Concurrency testing for crash-absence.** By integrating with Shuttle, you can run your actions under a randomized thread scheduler, testing that your system doesn't panic or deadlock under concurrent access. This verifies crash-absence, not full linearizability — but it catches data races and deadlocks that sequential tests miss. Neither `quickcheck-lockstep` nor Hedgehog offers this. The concurrent module supports configurable split strategies (`RoundRobin` or `Random { seed }` for reproducible randomized splits), an arbitrary number of concurrent branches via `branch_count`, per-branch trace collection on panic, and an optional final state check via `lockstep_concurrent_with_check` for verifying SUT consistency after concurrent operations.

**Async SUT support.** If your system-under-test is async (a database client, an HTTP service), `proptest-lockstep` supports async execution via the `async` feature flag. The model stays synchronous — it's a pure data structure — while the SUT runs under your async runtime. Note: the async path currently does not support shrinking of failing sequences, so counterexamples will be full-length.

---

## What Rust Programmers Get

If you're interested in Rust's type system more broadly, `proptest-lockstep` is a case study in several techniques that are individually well-known but rarely combined:

**GATs as HKT simulation.** The `Phase` trait, with `type Var<T>`, gives us type-constructor polymorphism without higher-kinded types. This pattern is applicable anywhere you need to parameterise a data structure by a "mode" that changes how contained values are represented — protocol states, serialization phases, compilation stages.

**Type equality witnesses for GADT simulation.** The `Is<A, B>` pattern, combined with an enum whose variants carry witnesses, gives exhaustive matching with per-arm type refinement. This has applications far beyond testing — expression evaluators, typed serialization formats, protocol state machines, and typed command patterns.

**Composable trait algebras.** The bridge system shows how to build a "language" of type-level combinators using Rust's trait system. Each bridge combinator is a struct with trait implementations that compose with other combinators, and the compiler verifies the composition. This pattern applies anywhere you have pairs of related types that need to be processed in parallel — serialization, schema migration, and data transformation pipelines.

**Sealed trait DSLs.** The `Op<A, B>` projection language is a tiny embedded DSL whose programs are type-checked by the Rust compiler. Zero-sized types implement the operations, compositions are checked at compile time, and the whole thing compiles down to nothing at runtime. The extra type parameter on `OpComp` is a concession to Rust's type inference — Haskell hides the intermediate type, Rust makes it explicit — but the compile-time verification is identical.

---

## The Cost

No design is free. Here's what you trade:

**A proc macro.** The `#[lockstep_actions]` attribute generates a significant amount of code: a GADT enum, a visitor trait, an `AnyAction` wrapper with bridge dispatch and variable storage, typed interpreter traits, and dispatch helpers. If something goes wrong in the generated code, the errors can be confusing. `cargo expand` is your friend.

**One encapsulated `unsafe`.** The `Is<A, B>` witness uses an `unsafe` pointer cast internally (`ManuallyDrop` + `ptr::read`). The soundness argument is airtight — the witness is only constructible via `refl()` at the identity type, and the variance choice (`PhantomData<fn(A) -> B>`) prevents subtyping exploits. It's encapsulated in the library — users never write unsafe code. But it's there.

**Annotation overhead.** Each action requires `real_return` and `bridge` annotations (and `model_return` when the model type differs). These are string-encoded types in the attribute, which means error messages point to the macro invocation rather than the specific type. The bridge names can be short (`Transparent`, `Opaque`, etc.) thanks to auto-imported preludes, but there's no escaping the fact that you're encoding type relationships in strings.

**`OpComp` has three type parameters.** Where Haskell's `OpComp` has two (`OpComp f g`), the Rust version needs a third for the intermediate type: `OpComp<F, G, Mid>`. This is because Rust can't infer unconstrained type parameters on a struct. In practice, a type alias hides this — `type HandleProj = OpComp<OpOk, OpFst, (FileHandle, String)>` — but it's a visible departure from the Haskell original.

**Learning curve.** The bridge algebra, the `GVar` projections, and the phase distinction are concepts that take time to internalize. I've tried to make the simple case simple (transparent types need only `real_return` and `bridge`) and the complex case possible (opaque handles, compound projections). But this is a library for people who care about correctness, and correctness has a vocabulary.

**Existential boundary.** To store actions with different return types in a single `Vec`, we use a trait object (`Box<dyn AnyAction>`). All typed logic lives inside the boundary; the dynamic dispatch is only for iterating the sequence. But it means you can't directly pattern-match on the sequence from outside the framework.

---

## Lineage

`proptest-lockstep` stands on the shoulders of a long chain of ideas:

- **QuickCheck** (Claessen & Hughes, 2000) introduced property-based testing.
- **Hedgehog** brought integrated shrinking, symbolic/concrete variable tracking, and parallel state machine testing to the Haskell ecosystem.
- **quickcheck-dynamic** (IOG & QuviQ) provided a minimal core for stateful testing in Haskell, with dynamic logic support.
- **quickcheck-lockstep** (Edsko de Vries, Well-Typed, 2022) layered the lockstep abstraction on top — the insight that "model and system agree" is the only postcondition you need. It's used in Well-Typed's consulting and training work.
- **falsify** (de Vries, 2023) advanced internal shrinking for Haskell, addressing limitations of both QuickCheck's manual approach and Hedgehog's integrated approach.
- **proptest** brought Hypothesis-inspired testing to Rust, with per-value strategies and integrated shrinking.
- **proptest-state-machine** (Zemanovič) added state machine strategies to proptest, inspired by Erlang's eqc_statem.
- **Shuttle** (AWS) and **loom** (Tokio) provided concurrency testing infrastructure unique to the Rust ecosystem.

I took the lockstep idea, the phase distinction, and the variable projection DSL, and rebuilt them for Rust's type system. Where Haskell uses GADTs, I use type equality witnesses. Where Haskell uses HKT, I use GATs. Where Haskell uses manual shrinking, I lean on proptest's integrated approach. And where Haskell has no answer, I integrate with Shuttle for concurrent crash-absence testing.

The **bridge algebra is a new contribution**, not a port. In Haskell's `quickcheck-lockstep`, users define two GADTs manually — `ModelValue` and `Observable` — with one constructor per type shape in their API. For a file system with five return types, that's ten GADT constructors plus two interpretation functions. The bridge algebra replaces all of this with composable combinators: `Transparent`, `Opaque`, `ResultBridge`, `TupleBridge`, `OptionBridge`, `VecBridge`. You describe the observability structure *declaratively*, and the compiler verifies that the bridge connects the right types. This is less code, more composable, and catches errors earlier.

The **`resolve_model_gvar` function** is another addition with no Haskell counterpart. In `quickcheck-lockstep`, the model and SUT share a single variable environment because Haskell's `ModelValue` GADT handles the type mapping. In `proptest-lockstep`, the model and SUT have separate environments (a cleaner architecture), and `resolve_model_gvar` provides the model-side lookup when types differ due to opaque handles.

The **Op DSL** is adapted from the Haskell original but differs in one key way: projections return `Option<B>` (partial projections) rather than being total. This means `OpOk` on an `Err` value returns `None` rather than panicking, and the framework handles the failure gracefully during variable resolution.

---

## Try It

```toml
[dev-dependencies]
proptest-lockstep = "0.1"
proptest = "1"
```

The repository includes two worked examples: a key-value store (the simplest case — all transparent types, no handles) and a file system (the full case — opaque handles, GVar projections, composed bridges). The proc macro handles the heavy lifting — generating the GADT enum, visitor trait, bridge dispatch, variable storage, and typed interpreter traits. For simple cases, you're looking at maybe 50 lines of code beyond the model itself.

For something that gives you exhaustive, compile-time-verified, automatically-shrunk, optionally-concurrent stateful property tests — I think that's a good trade.
