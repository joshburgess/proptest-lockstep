# Type Theory Analysis: proptest-lockstep

## 1. How the Encoding Compares to the State of the Art

### The Leibniz Witness (`Is<A,B>`)

The encoding uses **Leibniz equality** -- going back to Martin-Lof. In Haskell, this is `Data.Type.Equality.:~:`. Leibniz equality states:

> *a = b* iff for all predicates *P*, *P(a)* implies *P(b)*

`Is<A,B>` is exactly this, projected down to Rust:

```
Is<A,B> ~ forall F. F<A> -> F<B>
```

The `lift` operation corresponds to the **congruence rule** for type equality (if `A = B`, then `F A = F B` for any `F`). Making it `pub(crate)` is the correct call -- Rust lacks higher-kinded types, so there's no way to syntactically enforce that `FA` is genuinely `F<A>`. The restriction to crate-internal usage maintains the soundness invariant **by administrative fiat** rather than by the type system itself. This is a known limitation of simulating GADTs in languages without first-class type equality.

**Comparison to prior art:**
- **Haskell's `:~:`** gives you `gcastWith :: (a :~: b) -> (a ~ b => r) -> r` -- the cast goes through GHC's constraint solver, which is sound by construction. Our cast goes through `unsafe` pointer transmute, which is sound by the construction discipline on `refl()`. Same metatheoretic property, different enforcement mechanism.
- **OCaml's type-eq trick** (GADT branches returning `(a, b) eq`) works similarly but without `unsafe`, because OCaml's match semantics do the refinement.
- **Scala 3's `=:=[A,B]`** is the closest analogue -- it also uses an opaque type with a `refl` constructor and runtime cast.

The encoding sits at the **practical ceiling** of what Rust can express without language-level GADT support.

### The Phase GAT

The `Phase` trait with `type Var<T: 'static>` is a **defunctionalized type family**:

```
Phase : * -> *
Phase.Var : Phase -> (* -> *)
```

Where:
- `Symbolic.Var<T> = SymVar<T>` -- an opaque token (an index into a typing context)
- `Concrete.Var<T> = ConVar<T>` -- a wrapped runtime value

This is a **modal type distinction**. Through the lens of **staged computation** (MetaML, Davies-Pfenning modal type theory):

```
Symbolic ~ Box   (the "next stage" / "code" modality)
Concrete ~ Dia   (the "current stage" / "value" modality)
```

A `SymVar<T>` is a *name* for a future value of type `T` -- exactly a Box(T). A `ConVar<T>` is a value that exists *now* -- exactly a Dia(T) (though trivially, since the value is present, this degenerates to just T).

**Key insight**: The Phase GAT enforces a **staged correctness property** -- you cannot observe a value during generation, and you cannot refer to a symbolic name during execution. This is the same invariant that Davies-Pfenning's modal lambda calculus enforces, but without the full modal type theory machinery.

**Comparison to Haskell:**
- Haskell's `quickcheck-lockstep` uses a type family `type family ModelValue state action` which serves a similar purpose but is less cleanly separated. The Phase approach is more principled -- it's a uniform, parametric distinction rather than an ad-hoc per-action type family.
- This is arguably **more expressive than the Haskell approach** because the phase parameter flows through the entire system uniformly. In Haskell, you'd achieve this with a GADT-indexed action type, but you'd need `DataKinds` + `TypeFamilies` + `GADTs` working together.

### The Projection Chain (`Op`, `GVar`, `OpComp`)

The `Op` trait defines a **partial lens** (or, more precisely, an **affine traversal**):

```
Op<A,B> ~ A -> Maybe B
```

`OpComp` is Kleisli composition in the `Maybe` monad:

```
OpComp<F, G, B> ~ A --(F)--> Maybe B --(G)--> Maybe C
                = A --(F >=> G)--> Maybe C
```

The `GVar<X, Y, O>` bundles a variable with its projection:

```
GVar<X, Y, O> ~ (SymVar<X>, O : Op<X, Y>)
             ~ (Name X, X -/-> Y)
```

This is a **dependent pair** -- the projection operation is statically typed to match the variable's stored type. The `then` combinator gives you composition:

```
then : GVar<X, Y, O> -> (P : Op<Y, Z>) -> GVar<X, Z, OpComp<O, P, Y>>
```

**What's novel here**: Haskell's `quickcheck-lockstep` has nothing like this. In Haskell, you'd typically pattern-match on the `ModelValue` in the interpreter and construct the handle manually. The projection chain approach is:
1. **More compositional** -- projections chain without per-case boilerplate
2. **Type-safe at the point of use** -- the type checker ensures the projection chain is valid
3. **Extensible** -- new projections (like `OpIndex`) can be added without modifying existing code

From a type theory perspective, this is an **internal language for partial lenses** embedded in Rust's type system.

### The Explicit Intermediate Type `B` in `OpComp`

The three-parameter `OpComp<F, G, B>` deserves note. In Haskell, you'd write:

```haskell
data OpComp f g where
  OpComp :: f a b -> g b c -> OpComp f g a c
```

The intermediate type `b` is existentially quantified inside the GADT. In Rust, there are no existentials, so `B` must be visible as a type parameter. This is **not a weakness** -- it's a different point in the design space. The explicit `B` means:
- Type inference doesn't have to guess the intermediate type (important because Rust's inference is weaker than Haskell's)
- The full type is visible at use sites, which aids debugging
- The cost is verbosity in type aliases (e.g., `type HandleProj = OpComp<OpOk, OpFst, (FileHandle, String)>`)


## 2. Curry-Howard Connections in the Bridge Algebra

### Bridges as Relations (Logical Relations, Reynolds 1983)

A bridge `B : LockstepBridge` is a **binary relation** between two types:

```
[[B]] <= B.Real x B.Model
(r, m) in [[B]]  iff  B.observe_real(r) = B.observe_model(m)
```

The Lean formalization captures this exactly:

```lean
def bridge_equiv (b : Bridge R M) (r : R) (m : M) : Prop :=
  b.observe_real r = b.observe_model m
```

### The Lifts as Logical Relation Closure Properties

| Rust Bridge | Logical Relation Rule | Lean Theorem |
|---|---|---|
| `Transparent<T>` | Delta_T (identity/diagonal) | `transparent_refl` |
| `Opaque<R,M>` | Top (trivial/total) | `opaqueBridge_always` |
| `ResultBridge<B1,B2>` | [[B1]] + [[B2]] (sum) | `sum_preserves_ok/err` |
| `TupleBridge<B1,B2>` | [[B1]] x [[B2]] (product) | `prod_preserves`, `prod_equiv_iff` |
| `OptionBridge<B>` | 1 + [[B]] (lifted) | `option_preserves_some/none` |
| `VecBridge<B>` | mu X. 1 + [[B]] x X (list) | `list_preserves_nil/cons` |

This is the **fundamental theorem of logical relations**: the relation is closed under all type constructors. This is what Reynolds proved in '83 for System F, and what the Lean formalization proves for this particular algebra.

### Curry-Howard Reading

Under Curry-Howard:
- A **bridge** is a **proof rule** for establishing a relation between types
- **Transparent** is the **reflexivity axiom** (Delta)
- **Opaque** is the **truth axiom** (Top-intro)
- The **lifts** are **structural rules** that build compound proofs from component proofs
- The **check** method is **proof checking** -- it decides whether the relation holds on particular witnesses
- The **fundamental theorem** is the **admissibility lemma** -- every compound type has a bridge, and it's determined compositionally by its structure

### Bridges as Spans (Category-Theoretic Reading)

There's an even deeper reading. A bridge `B` defines two maps:

```
observe_real  : B.Real  -> B.Observed
observe_model : B.Model -> B.Observed
```

This is a **span** in the category **Set**:

```
   B.Observed
   /         \
B.Real    B.Model
```

The pullback of this span gives the relation [[B]]. When `B.Observed` is equipped with equality, this pullback is exactly `bridge_equiv`.

For **Transparent**, the span is:

```
      T
    /   \
   T     T       (both legs are identity)
```

The pullback is the diagonal Delta_T = {(t,t) | t in T} -- equality.

For **Opaque**, the span is:

```
      1
    /   \
   R     M       (both legs are the unique map to 1)
```

The pullback is R x M (everything is related) -- the trivial relation.

This span perspective explains why the bridge algebra is so clean: we're working in a category where the objects are types and the morphisms are observation functions, and the bridges are the **spans with decidable equality at the apex**. The lifts preserve the span structure functorially.


## 3. Lean Formalization: Level of Abstraction

**Assessment: Correct level for a workshop paper, with one important caveat.**

### What It Gets Right

The formalization captures the **essential algebraic structure** -- that the bridge is a logical relation closed under sum, product, option, and list, with the bounded bisimulation as the connection to testing. The `bounded_bisim_mono` theorem is the key non-trivial result: it says that deeper testing gives strictly stronger guarantees.

The `LockstepSystem` structure in Lean faithfully models the Rust architecture:
- `ActionIdx` as the type of actions
- `RetS/RetM` as dependent return types (this is genuinely dependent -- the return type depends on the action index!)
- `bridge` as a per-action bridge assignment
- `step_model/step_sut` as the interpreters

### The Abstraction Gap

The REVIEW.md correctly identifies: the formalization stops at the algebra. The connection between `bounded_bisim` and the test runner is informal. Specifically:

1. **The runner establishes bounded_bisim** -- this is claimed but not proved. To prove it, you'd need to model `LockstepSut::apply` in Lean and show that a successful execution of `n` steps implies `bounded_bisim n s0 r0`.

2. **Preconditions weaken the universal quantifier** -- the Lean formalization quantifies over ALL actions (`forall a : ActionIdx`), but the test runner only checks actions that pass the precondition. The actual guarantee is:

```
bounded_bisim_with_preconditions n P sm ss :=
  forall a, P(a, sm) -> ...
```

This is a strictly weaker statement. Whether this matters depends on whether the precondition is "physical" (the action genuinely can't happen) or "logical" (it can happen but we choose not to test it).

3. **The TypedEnv is not modeled** -- variable resolution happens at the metalevel (Lean's `let` bindings), not inside the formalization. This means the proof doesn't capture bugs in the variable resolution machinery.

### Recommendations

**Option A: Formalize the one-step lemma.** Model the runner's `apply` as a function in Lean:

```lean
def runner_step (sys : LockstepSystem) (a : sys.ActionIdx) (sm : sys.SM) (ss : sys.SS)
    (success : bridge_equiv (sys.bridge a) (sys.step_sut a ss).2 (sys.step_model a sm).2) :
    bounded_bisim sys 1 sm ss
```

This closes the simplest part of the gap -- showing that a single successful step establishes `bounded_bisim 1`.

**Option B: Frame the gap explicitly as a design principle.** The separation between "algebraic properties we CAN prove" and "operational properties we TRUST" is itself interesting. You could argue that the bridge algebra is the **specification**, and the runner is the **implementation**, and they're related by a **refinement** that happens to be too complex for current tools. This is honest and publishable.


## 4. Type-Theoretic Extensions (Ordered by Impact)

### Extension 1: Polynomial Functor Bridge Derivation (HIGH IMPACT, FEASIBLE)

The bridges follow the structure of polynomial functors:

```
Every Rust type T = 1 | T1 + T2 | T1 x T2 | mu X. F(X)
```

A bridge for T can be **automatically derived** from T's structure:
- `1` gets `UnitBridge`
- `T1 + T2` gets `ResultBridge<B1, B2>` (or `EitherBridge`)
- `T1 x T2` gets `TupleBridge<B1, B2>`
- `mu X. F(X)` gets a recursive bridge

This is the **generic programming** approach (Hinze, 2000; Gibbons, 2006). A derive macro could generate bridges automatically:

```rust
#[derive(LockstepBridge)]
#[bridge(FileHandle => MockHandle: opaque)]
struct OpenResult {
    handle: FileHandle,
    path: String,
}
```

The theoretical basis is that **logical relations for polynomial functors are themselves polynomial**, so the bridge derivation is structurally recursive.

### Extension 2: Session-Typed Action Sequences (HIGH IMPACT, HARD)

The current system generates arbitrary action sequences subject to preconditions. What if the type system could enforce valid sequences?

```rust
trait SessionPhase: Phase {
    type Protocol;  // A session type
    type Var<T: 'static>;
}
```

Where `Protocol` is something like:

```
OpenSession = Send<Open, Recv<Handle, FileSession>>
FileSession = Choose<
    Send<Write(Handle, Data), Recv<Result, FileSession>>,
    Send<Close(Handle), Recv<Result, End>>,
>
```

This would make invalid action sequences **unrepresentable** rather than filtered by preconditions. The bridge algebra would extend naturally -- each session type step would carry its bridge.

**Why this is hard**: Session types need linear/affine usage of channels. Rust has the affine story (ownership), but composing session types with random generation is an open problem. You'd need to generate valid session traces, which is itself a non-trivial exploration of the session type's topology.

### Extension 3: Graded Bridges (MEDIUM IMPACT, FEASIBLE)

Currently, `Opaque` is a binary choice -- either fully observable or completely opaque. A **graded** spectrum:

```rust
trait GradedBridge {
    type Grade: Monoid;  // e.g., security level, precision level
    type Real;
    type Model;
    type Observed;
    fn grade(&self) -> Self::Grade;
    fn observe_real(&self, r: &Self::Real) -> Self::Observed;
    fn observe_model(&self, m: &Self::Model) -> Self::Observed;
}
```

Where the grade tracks *how much* information the observation reveals. This connects to:
- **Graded monads** (Orchard et al.) -- the grade forms a monoid
- **Information flow types** (Volpano-Smith-Irvine) -- the grade is a security level
- **Approximate observation** -- the grade could measure precision

The lifts would be **graded monoidal functors**: the product bridge's grade is the product of component grades.

### Extension 4: Dependent Bridges (LOW FEASIBILITY, HIGH NOVELTY)

The `LockstepSystem` in Lean already uses dependent types:

```lean
RetM : ActionIdx -> Type
RetS : ActionIdx -> Type
bridge : (a : ActionIdx) -> Bridge (RetS a) (RetM a)
```

The bridge depends on the action! This is a **dependent logical relation**. In Rust, this dependence is simulated through the proc macro -- each action variant carries its own bridge type. But there's a deeper structure:

The bridges form a **fibration** over the action space:

```
Bridge
  |
  | pi
  v
ActionIdx
```

Where the fiber over action `a` is `Bridge (RetS a) (RetM a)`. The fundamental theorem is a **fibrewise** property: each fiber satisfies the logical relation closure conditions.

This perspective suggests a generalization: instead of indexing bridges by actions alone, you could index them by **states** too:

```lean
bridge : (a : ActionIdx) -> sys.SM -> Bridge (RetS a) (RetM a)
```

This would allow **state-dependent observation granularity** -- for example, observing more detail about a file handle after the file has been opened and written to. The bisimulation would need to track bridge variation across states, making the monotonicity proof more interesting.


## Summary

| Dimension | Assessment |
|-----------|-----------|
| **GADT encoding** | At Rust's practical ceiling; `Is<A,B>` is sound, `lift` restriction is the right call |
| **Phase GAT** | Clean modal type distinction; more principled than Haskell's approach |
| **Projection chains** | Novel; nothing comparable in Haskell ecosystem; typed partial lenses |
| **Bridge algebra** | Reynolds-style logical relation; clean Curry-Howard reading as spans with decidable apex |
| **Lean formalization** | Right level for workshop paper; the algebraic properties are the correct things to prove |
| **Most impactful extension** | Polynomial functor bridge derivation -- feasible, would differentiate from all prior work |
| **Most novel extension** | State-dependent bridges (dependent logical relations over the product of action and state spaces) |


## References

- Reynolds, J.C. (1983). Types, Abstraction and Parametric Polymorphism.
- Davies, R. and Pfenning, F. (2001). A Modal Analysis of Staged Computation.
- Hinze, R. (2000). A New Approach to Generic Functional Programming.
- Gibbons, J. (2006). Datatype-Generic Programming.
- Orchard, D., Wadler, P., and Eades, H. (2019). Unifying graded and parameterised monads.
- Volpano, D., Smith, G., and Irvine, C. (1996). A Sound Type System for Secure Flow Analysis.
- de Vries, E. (2021). quickcheck-lockstep: Testing stateful systems with lockstep-style property tests.
