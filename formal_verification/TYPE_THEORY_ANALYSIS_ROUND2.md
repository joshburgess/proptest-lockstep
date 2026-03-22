# Type Theory Analysis — Round 2

## 1. Rust ↔ Lean Correspondence: Alignment and Divergence

### Where They Align

The Lean `Bridge` structure faithfully captures the essential content of the Rust `LockstepBridge` trait:

| Rust | Lean | Alignment |
|------|------|-----------|
| `LockstepBridge::Real` | `R` (param of `Bridge R M`) | Exact |
| `LockstepBridge::Model` | `M` (param of `Bridge R M`) | Exact |
| `LockstepBridge::Observed` | `Bridge.Observed` (field) | Exact |
| `observe_real(&R) → Observed` | `observe_real : R → Observed` | Exact (modulo reference) |
| `observe_model(&M) → Observed` | `observe_model : M → Observed` | Exact |
| `PartialEq` on `Observed` | `dec_eq : DecidableEq Observed` | **Stronger in Lean** |
| `check(r, m) → Result<(), String>` | `bridge_equiv b r m : Prop` | Lean separates computation from specification |

The `bridge_equiv_decidable` instance explicitly bridges this last gap: it shows that the propositional `bridge_equiv` is computationally decidable, which is exactly what `check` computes in Rust.

The `LockstepSystem` structure in Lean captures the essence of `LockstepModel`:

| Rust | Lean | Notes |
|------|------|-------|
| `LockstepModel::ModelState` | `SM` | |
| `LockstepModel::Sut` | `SS` | |
| `step_model(&mut S, &dyn AnyAction, &TypedEnv) → Box<dyn Any>` | `step_model : ActionIdx → SM → SM × RetM a` | **Major divergence** |
| `step_sut(&mut S, &dyn AnyAction, &TypedEnv) → Box<dyn Any>` | `step_sut : ActionIdx → SS → SS × RetS a` | Same |

### Where They Diverge

**1. The TypedEnv gap is the most significant divergence.** The Rust runner threads a `TypedEnv` through every step, storing action results and resolving GVar projection chains for subsequent actions. The Lean model has pure functions `SM → SM × RetM a` with no environment threading. This means the Lean model cannot express:
- GVar projection chains (`GVar::new(var, OpOk).then(OpFst)`)
- Variable resolution failures (`resolve_gvar` returning `None`)
- The interaction between stored opaque handles and later actions

This is not an oversight — it's a deliberate simplification. Modeling TypedEnv in Lean would require existential types (for the heterogeneous store) and partial functions (for downcasts), which would dramatically complicate the formalization. The trade-off is correct for a pearl, but it means the formal guarantee applies to an idealized system.

**Type-theoretic insight**: The Rust TypedEnv is essentially a dependently-typed heterogeneous map keyed by `(usize, TypeId)`. The `get` operation performs a runtime type check that corresponds to a dependent pattern match. Formalizing this in Lean would require a universe-polymorphic heterogeneous list indexed by a list of types — exactly the construction that makes dependently-typed programming hard.

**2. The `Is<A,B>` witness exists in Rust but not in Lean.** The Lean `LockstepSystem` doesn't need GADTs because it uses dependent types directly: `RetM : ActionIdx → Type` gives each action its own return type. In Rust, `RetM` is an associated type per action, and the `Is<A,B>` witness is needed to bridge the gap between the existential `Box<dyn Any>` and the concrete type. This is a classic example of how dependent types eliminate the need for type-equality witnesses.

**3. Phase GAT (`Symbolic`/`Concrete`) is absent from the Lean formalization.** The Lean model doesn't need phase separation because it doesn't model test generation — only test execution and checking. The phase distinction is a Rust engineering feature, not a metatheoretic property.

## 2. Bridge Algebra as a Logical Relation: Completeness Assessment

The bridge algebra is presented as a logical relation in the sense of Reynolds (1983). Let me assess this claim precisely.

### What Reynolds' logical relations give you

A logical relation is a type-indexed family of relations {R_τ}_{τ ∈ Type} satisfying:
1. **Closure under type constructors**: if R_τ(a, b) and R_σ(c, d), then R_{τ×σ}((a,c), (b,d))
2. **The identity extension lemma**: at base types, the relation is equality
3. **The abstraction theorem**: parametrically polymorphic functions preserve the relation

### What the bridge algebra provides

1. **Closure under type constructors**: ✅ Proved for `Sum`, `Prod`, `Option`, `List`. Each lift theorem shows that component bridge-equivalence implies composite bridge-equivalence. The `BridgeRefinement.lean` monotonicity theorems show that this closure is also functorial (it preserves the refinement ordering).

2. **The identity extension lemma**: ✅ `transparent_equiv_is_eq` proves that `Transparent` bridge-equivalence is ordinary equality. `transparent_refl` proves reflexivity. These are exactly the identity extension lemma for the bridge relation at "transparent" base types.

3. **The abstraction theorem**: ⚠️ **Partially proved.** The `observational_refinement_equiv` theorem is the closest analog:
   ```
   bounded_bisim n sm ss ↔ ∀ (pre : List ActionIdx) (a : ActionIdx),
     pre.length + 1 ≤ n →
     sut_observation a (sut_state_after pre ss) = model_observation a (model_state_after pre sm)
   ```
   This says bounded bisimulation is equivalent to observational indistinguishability through the bridge algebra. But it's not quite Reynolds' abstraction theorem because:
   - It quantifies over *traces* (sequences of actions), not over *contexts* (arbitrary programs)
   - It's bounded by depth n, not universally quantified
   - It's specific to the lockstep testing scenario, not stated for arbitrary bridged computations

   The full Reynolds abstraction theorem would say: *for any program P that interacts with the system only through bridged observations, P cannot distinguish the SUT from the model*. The trace-based formulation is a special case where "programs" are linear sequences of actions.

### What's missing for completeness

- **Function type closure**: There's no bridge for function types `A → B`. In the lockstep setting this isn't needed (actions are data, not higher-order), but for a full logical relation you'd need `(A → B)` lifted to `(RA → RB) ↔ (MA → MB)`.
- **Recursive type closure**: `listBridge` handles `List` (the free monoid), but there's no general fixed-point bridge for arbitrary recursive types.
- **Higher-kinded bridge lifting**: The current lifts are first-order — one per type constructor. A general `map_bridge : (F : Type → Type) → Bridge A B → Bridge (F A) (F B)` would require HKT, which neither Rust nor Lean directly supports (though Lean comes closer via universes).

### Verdict

The bridge algebra is a *first-order fragment* of a logical relation: it covers polynomial functors (sums, products, option, list) with transparent and opaque leaves. This is exactly the right scope for a testing tool — higher-order bridges would be overengineering. For the pearl framing, describing this as "the polynomial fragment of Reynolds' logical relation" is both accurate and compelling.

## 3. BridgeSpec and Polynomial Derivation

### The Abstraction

`BridgeSpec` is an inductive type describing the *shape* of a derived bridge:

```lean
inductive BridgeSpec where
  | transparent | opaque | unit
  | sum (ok err : BridgeSpec) | prod (fst snd : BridgeSpec)
  | option (inner : BridgeSpec) | list (inner : BridgeSpec)
```

This is the free algebra over the polynomial bridge operations — it's the *syntax* of bridge composition. The proc macro's `derive_bridge` function maps a pair of Rust types to a `BridgeSpec` (conceptually), and then the `BridgeSpec` is realized as a concrete `Bridge R M`.

### The Gap

The critical missing piece is the **interpretation function** connecting `BridgeSpec` to concrete `Bridge` values. The natural type would be:

```lean
def interp (spec : BridgeSpec) (types : spec → Type × Type) :
    Bridge (types spec).1 (types spec).2
```

But this requires `types` to be a *dependent* function mapping each leaf of the spec to a pair of types — and the relationship between the spec's structure and the type structure is hard to express without something like a universe of codes à la generic programming.

The alternative approach (which `DerivedBridge.lean` takes) is to state the properties of each combinator individually without a unifying interpretation. This works — the theorems are correct — but it means `BridgeSpec` is ornamental: it describes shapes but doesn't participate in the proofs.

### Suggestions

For the pearl, either:
1. **Remove `BridgeSpec`** and state the polynomial derivation as a meta-theorem: "any bridge built from `transparent`, `opaqueBridge`, `sumBridge`, `prodBridge`, `optionBridge`, `listBridge` preserves `bridge_equiv` by structural induction." The existing lift theorems are the inductive cases; the base cases are `transparent_refl` and `opaqueBridge_always`. No new Lean code needed.
2. **Upgrade `BridgeSpec` with a universe of codes.** Define a dependent type that maps specs to concrete types and bridges:
   ```lean
   def BridgeUniverse (spec : BridgeSpec) : Type × Type × Bridge ...
   ```
   This is substantial work but would make the polynomial derivation formally precise.

Option 1 is appropriate for a pearl. Option 2 is a research contribution in itself (generic programming for logical relations).

## 4. Bridge Refinement: Preorder vs. Lattice

### Current State: Preorder

`bridge_refines` is defined as containment of `bridge_equiv`:

```lean
def bridge_refines (b1 b2 : Bridge R M) : Prop :=
  ∀ (r : R) (m : M), bridge_equiv b1 r m → bridge_equiv b2 r m
```

This is reflexive (`refines_refl`) and transitive (`refines_trans`), making it a preorder. The bounds are:
- Bottom: `opaque` (everything refines it — `opaque_coarsest`)
- Top: `transparent` for uniform bridges (`transparent_refines_uniform`)

### Why It's Not a Lattice

For a lattice, you'd need meets (greatest lower bounds) and joins (least upper bounds). The **meet** of two bridges `b1, b2 : Bridge R M` would be the finest bridge coarser than both — the bridge whose equivalence classes are the intersections of `b1`'s and `b2`'s equivalence classes. But `Bridge R M` is existentially quantified over `Observed`, so meeting two bridges requires constructing a *new* observed type. Specifically:

```
Observed_meet = { (o1, o2) | observe_real_1(r) = o1 ∧ observe_real_2(r) = o2 }
```

This is the product of the two observed types, with the observation being the pairing. For the **join** (coarsest bridge finer than both), you'd need the *coequalizer* or quotient of the observed types. This requires quotient types, which Lean supports via `Quotient` but which add complexity.

### Should It Be Strengthened?

For the testing story, the preorder is sufficient. The lattice structure would be needed if you wanted to:
- **Automatically combine bridges** from different sources (e.g., merging the observation from two tests)
- **Compute the optimal bridge** for a given pair of types

Neither of these arises in the current workflow: the user (or the proc macro) picks a single bridge per action. The preorder is used only for the `refines_strengthen_bisim` theorem, which says "finer bridges give stronger guarantees."

**Recommendation**: Note the lattice structure in the pearl as a direction for future work, but don't implement it. The preorder is the right level of abstraction for the current system.

## 5. Observational Refinement vs. Reynolds' Abstraction Theorem

### Reynolds' Abstraction Theorem (1983)

For any type `τ` and any logical relation `R`:
- If `f : ∀α. τ(α)` is parametrically polymorphic, then `f` respects `R`: `R_τ(f[A], f[B])`.

This says: parametric polymorphism implies relational preservation. The key word is *parametric* — the function doesn't inspect the type argument.

### The proptest-lockstep Analog

`observational_refinement_equiv` says:
```
bounded_bisim n sm ss ↔ ∀ (pre : List ActionIdx) (a : ActionIdx),
  pre.length + 1 ≤ n →
  sut_observation a (sut_state_after pre ss) = model_observation a (model_state_after pre sm)
```

This is a *trace-indexed* version of Reynolds' theorem. The "program" is a sequence of actions (a trace), and the "parametric function" is the observation at each step. The bridge plays the role of the logical relation. The theorem says: if the logical relation holds at every step along every trace up to depth n, then the bisimulation holds — and vice versa.

### Key Differences

1. **Traces vs. contexts**: Reynolds quantifies over all contexts (programs with a hole); proptest-lockstep quantifies over all traces (linear sequences of actions). Traces are a proper subset of contexts — a context could branch, loop, or compute on intermediate results. In the lockstep setting, this restriction is natural because the test runner executes a linear sequence.

2. **Bounded vs. unbounded**: Reynolds' theorem is universally quantified; the proptest-lockstep version is bounded by depth n. This reflects the reality of testing: you can only check finitely many steps. The `lockstep_bisim` (full coinductive bisimulation) is the limit, but it can't be established by testing.

3. **First-order observations**: Reynolds' relation works for higher-order types (functions). The bridge algebra only works for first-order types (data). This is appropriate — test results are data, not functions.

### The Deep Insight

The bridge algebra is a *decidable fragment* of Reynolds' logical relation: it's restricted to polynomial functors (first-order data types) with decidable equality on observations. This decidability is exactly what makes it testable — you can compute `bridge_equiv` at runtime and report mismatches. A higher-order logical relation would be undecidable in general.

This is the pearl insight restated precisely: **lockstep testing is the computational content of a decidable logical relation.**

## 6. Type-Theoretic Insights from the Formalization

### Insight 1: The Bridge Structure is a Span

A `Bridge R M` with `Observed`, `observe_real : R → Observed`, `observe_model : M → Observed` is a **span** in category-theoretic terms:

```
        R ←—observe_real—— Observed ——observe_model—→ M
```

Bridge equivalence (`observe_real r = observe_model m`) is the **pullback** condition: `r` and `m` are related iff they map to the same observation. This is the same construction that gives you equivalence relations from surjections — the kernel pair.

The bridge lifts (sum, prod, option, list) are **functorial**: they lift spans to spans, preserving the pullback condition. This is exactly the statement of the fundamental theorem.

The bridge refinement ordering is the ordering on spans by factorization: `b1` refines `b2` iff there's a factorization `Observed1 → Observed2` making the triangle commute. The current formalization uses the weaker condition (containment of the pullback relation), which doesn't require the factorization to exist — just the implication on related pairs.

### Insight 2: Bounded Bisimulation is a Stratified Logical Relation

`bounded_bisim n` is a family of relations indexed by depth. At each level, it requires bridge-equivalence of results (the logical relation at the return type) AND the next level of relation at the successor states. This is exactly a **stratified logical relation** — common in step-indexed logical relations for programming language metatheory (Appel & McAllester, 2001).

The monotonicity theorem (`bounded_bisim_mono`) corresponds to the "monotonicity of step-indexing" property that step-indexed logical relations always satisfy.

### Insight 3: The Phase GAT is a Modal Type System

The `Phase` trait with `Symbolic`/`Concrete` and `type Var<T>` is essentially a **modal type system** with two modes:
- Symbolic mode (□): variables are opaque tokens, no observation possible
- Concrete mode (◇): variables hold real values, observation allowed

The transition from Symbolic to Concrete (test execution) is a **modality elimination**. The `Is<A,B>` witness plays the role of a **coercion proof** — evidence that the type `A` in one mode corresponds to type `B` in the other.

### Insight 4: GVar Projection Chains are Lenses

`GVar<X, Y, O>` with `OpComp<F, G, B>` is a **lens** — it focuses on a part of a composite value. The `Op` trait provides the getter (`apply : X → Option<Y>`), and the projection chain composition (`then`) is lens composition. The zero-sized type erasure means the lens is computed at compile time and erased at runtime — a classic application of GADTs for type-safe optimization.

## 7. Suggestions for Deepening the Foundations

### 7.1 State the Bridge Algebra as a Functor

The bridge algebra is a functor from the category of polynomial endofunctors to the category of spans with the pullback ordering. Stating this explicitly (even informally) would strengthen the pearl framing. The objects are `Bridge R M`, the morphisms are refinements, and the functorial action is the lift operations. The fundamental theorem says this functor preserves the pullback condition.

### 7.2 Connect to Step-Indexed Logical Relations

The `bounded_bisim` definition is a step-indexed logical relation. The testing completeness theorem (`testing_completeness`) corresponds to the "adequate observations separate programs" property in step-indexed models. Making this connection explicit would situate the work within the PL theory literature.

### 7.3 Formalize the Phase Transition

Model the Symbolic → Concrete transition as a functor between the two "mode" categories. The `Is<A,B>` witness is the morphism part of this functor. This would clarify the metatheory of the phase system and might reveal additional safety properties.

### 7.4 Explore Gradual Bridges

A "gradual" bridge would sit between Transparent and Opaque: `Gradual<R, M, F>` where `F : R → Partial<Observed>` is a partial observation function. This would give a lattice structure (transparent → gradual → opaque) and connect to the gradual typing literature. The `Partial<Observed>` type would distinguish "observation succeeded" from "observation not possible."

### 7.5 Bridge Algebra for Recursive Types

The current formalization covers `List` as a special case, but a general treatment of recursive types would use initial algebras. The bridge for `μX. F(X)` would be the initial algebra of the lifted functor `F̂` — the least fixed point of applying the bridge lift to `F`. This is exactly the construction used in parametricity proofs for recursive types (Pitts, 1998). For a follow-up paper, this would be a natural extension.

### 7.6 Effectful Bridges

The current bridges are pure: `observe_real : R → Observed`. An effectful bridge would allow `observe_real : R → M Observed` for some monad `M` (e.g., `IO` for observing real system state). This would connect to graded monads and effect-indexed logical relations, providing a formal framework for testing systems with observable effects beyond return values.
