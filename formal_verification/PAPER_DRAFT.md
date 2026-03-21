# Paper Draft: ICFP Functional Pearl

## Venue Analysis

### Option A: ICFP Functional Pearl -- "Bridges as Logical Relations" (STRONGEST)

The bridge algebra is the single cleanest idea. Story arc: "Haskell's quickcheck-lockstep uses a GADT to classify observations; we replace the GADT with a composable algebra that turns out to be a logical relation." The pearl does NOT need the concurrent module (DPOR, linearizability, loom). Those dilute the pearl story.

### Option B: ESOP/ECOOP Tool Paper (Strong, but needs benchmarks)

The full system is substantial but tool papers are judged on evidence. Needs: bug-finding case studies, performance benchmarks, comparison with Jepsen/PROPER/QuickCheck.

### Option C: ISSTA/ASE (Interesting but risky)

Testing venues want empirical results. Without bug-finding data on real systems, reviewers will say "nice idea, no evidence."

**Recommendation: Write the pearl first.** It requires the least additional work, it's the cleanest story, and it positions the library for a follow-up tool paper.

---

## Title

**Bridges Between Worlds: Composable Test Oracles as Logical Relations**

(Alternative: *Observational Refinement by Composition: A Bridge Algebra for Lockstep Testing*)

---

## Abstract (Draft)

Lockstep property testing verifies stateful systems by comparing a system-under-test (SUT) against a pure reference model. The central challenge is specifying *how* to compare: real and model return types may differ (opaque handles vs. mock identifiers), yet the comparison must be type-safe, compositional, and correct.

We present a *bridge algebra* -- a system of composable type-indexed combinators that specify observation at the boundary between real and model worlds. We show that this algebra is a *logical relation* in the sense of Reynolds: it is a type-indexed family of relations closed under sums, products, options, and lists. The *fundamental theorem* -- that each type constructor preserves bridge equivalence -- is proved in Lean 4 with zero unfinished proofs.

We connect the bridge algebra to testing via *bounded bisimulation*: a passing test at depth *n* establishes that the SUT and model are observationally equivalent up to *n* steps, at the granularity determined by the bridges. We prove monotonicity: deeper tests yield strictly stronger guarantees.

The bridge algebra replaces Haskell's `quickcheck-lockstep` approach of extending a monolithic GADT with a modular, compositional alternative. We implement it in Rust with a proc macro that eliminates boilerplate, and demonstrate it on examples including a file system with opaque handles and composed projections.

---

## Introduction Outline

### Opening hook (1 paragraph)

Property-based testing of stateful systems has a type problem: the system-under-test returns file handles, but the model returns integers. Haskell's `quickcheck-lockstep` solves this with a GADT that classifies each action's return type as observable, opaque, or compound. But GADTs don't compose: every new action requires extending the GADT, and compound return types require bespoke case analysis.

### The insight (1 paragraph)

We observe that the GADT is doing the work of a *logical relation* -- a type-indexed family of relations that respects type structure. Instead of a GADT, we define a *bridge algebra*: a small set of primitive bridges (transparent, opaque) and algebraic lifts (sum, product, option, list) that compose to handle any return type. The key property -- that composition preserves the relation -- is exactly the *fundamental theorem of logical relations*.

### Motivating example (1-2 paragraphs)

Show the file system example. The `Open` action returns `Result<(FileHandle, String), FsErr>` on the real side and `Result<(MockHandle, String), FsErr>` on the model side. The bridge is:

```
ResultBridge<
    TupleBridge<Opaque<FileHandle, MockHandle>, Transparent<String>>,
    Transparent<FsErr>
>
```

This reads compositionally: "On `Ok`, the first element is opaque (handle), the second is transparent (path); on `Err`, compare directly." No GADT extension needed.

### Contributions (bulleted list)

1. A *bridge algebra* for specifying test oracles compositionally, replacing Haskell's monolithic GADT approach (Section 2).
2. The observation that this algebra is a *logical relation*, with a machine-checked proof of the fundamental theorem in Lean 4 (Section 3).
3. A *bounded bisimulation* formulation of lockstep testing, with a machine-checked monotonicity proof (Section 4).
4. A *typed projection language* (GVar/Op) for decomposing compound return types into handle references, with Kleisli composition in the Maybe monad (Section 5).
5. An implementation in Rust with a proc macro that generates all bridge dispatch, variable storage, and typed interpreters from declarative annotations (Section 6).

---

## Section 2: The Bridge Algebra

**Definition 1 (Bridge).** A bridge B between types R (real) and M (model) consists of:
- A type Obs(B) of observations
- A function obs_R : R -> Obs(B) (real observation)
- A function obs_M : M -> Obs(B) (model observation)

**Definition 2 (Bridge equivalence).** Two values r : R and m : M are *bridge-equivalent*, written r ~_B m, when obs_R(r) = obs_M(m).

**Definition 3 (Primitive bridges).**
- *Transparent*: Delta(tau) where R = M = Obs = tau and both observations are the identity. Bridge equivalence is equality.
- *Opaque*: Top(R, M) where Obs = Unit and both observations return (). Bridge equivalence is trivially true.

**Definition 4 (Algebraic lifts).**
- *Sum*: Given B1 : Bridge(R1, M1) and B2 : Bridge(R2, M2), define B1 + B2 : Bridge(R1 + R2, M1 + M2) with observation by cases.
- *Product*: Given B1 and B2, define B1 x B2 : Bridge(R1 x R2, M1 x M2) with componentwise observation.
- *Option*: Given B, define B? : Bridge(R?, M?) with lifted observation.
- *List*: Given B, define [B] : Bridge([R], [M]) with pointwise observation.

The key visual -- show the bridge for the file system `Open` action as a tree:

```
       Result (Sum)
       /          \
    Ok             Err
     |              |
  Tuple          Transparent
  /    \          FsErr
Opaque  Transparent
Handle    String
```

---

## Section 3: The Fundamental Theorem

**Theorem 1 (Fundamental Theorem of Bridge Equivalence).** Each algebraic lift preserves bridge equivalence:

(a) If r ~_{B1} m then inl(r) ~_{B1+B2} inl(m).
(b) If r ~_{B2} m then inr(r) ~_{B1+B2} inr(m).
(c) If r1 ~_{B1} m1 and r2 ~_{B2} m2 then (r1,r2) ~_{B1 x B2} (m1,m2).
(d) If r ~_B m then Some(r) ~_{B?} Some(m).
(e) None ~_{B?} None.
(f) If ri ~_B mi for all i, then [r1,...,rn] ~_{[B]} [m1,...,mn].

**Theorem 2 (Variant Mismatch Detection).** The sum bridge detects variant mismatches: not(inl(r) ~_{B1+B2} inr(m)).

These are proved in Lean 4, file `Bridge.lean`, with zero `sorry`.

*Discussion:* Connect to Reynolds. The bridge algebra is exactly a logical relation for the type language {Unit, +, x, ?, []}. The fundamental theorem is the standard closure lemma. The novelty is the *application domain*: test oracles for stateful systems.

---

## Section 4: Bounded Bisimulation

**Definition 5 (Lockstep System).** A lockstep system S consists of:
- State types SM (model), SS (SUT)
- An action index type Act
- Dependent return types RetM, RetS : Act -> Type
- A per-action bridge: bridge : (a : Act) -> Bridge(RetS(a), RetM(a))
- Transition functions: stepM, stepS

Note: the return type depends on the action. This is genuinely dependent typing in the Lean formalization.

**Definition 6 (Bounded Bisimulation).**

```
bisim(S, 0, sm, ss) = True
bisim(S, n+1, sm, ss) = forall a : Act.
    let (sm', rm) = stepM(a, sm)
    let (ss', rs) = stepS(a, ss)
    rs ~_{bridge(a)} rm  /\  bisim(S, n, sm', ss')
```

**Theorem 3 (Monotonicity).** If bisim(S, m, sm, ss) and n <= m, then bisim(S, n, sm, ss).

**Interpretation:** A passing lockstep test of n steps establishes bisim(S, n, s0, r0). Longer tests are strictly stronger. For finite-state models, sufficiently deep testing converges to the full (coinductive) bisimulation.

---

## Section 5: Typed Projections

**The problem:** The `Open` action returns `Result<(FileHandle, String), FsErr>`. A subsequent `Write` action needs just the `FileHandle`. How do you reference a component of a prior result?

**Definition 7 (Projection).** A projection pi : tau_1 -/-> tau_2 is a partial function. Primitive projections: id, fst, snd, ok, err, some. Projections compose via Kleisli composition in Maybe:

```
(pi_1 ; pi_2)(v) = pi_1(v) >>= pi_2
```

**Definition 8 (Generalized Variable).** A GVar(x, pi) pairs a symbolic variable x : Var(tau_1) with a projection pi : tau_1 -/-> tau_2, yielding a reference of type tau_2 resolved at runtime.

*Connection to bridges:* When the action that produced the variable has an opaque bridge on the handle component, the projection extracts the opaque value. The bridge ensures this is safe: the handle's identity doesn't matter, only its behavioral equivalence when used later.

---

## Section 6: Implementation

Brief description of:
- The Rust implementation (bridge algebra as zero-cost trait impls)
- The proc macro (`#[lockstep_actions]` generates GADT enum, visitor trait, typed interpreters, bridge dispatch)
- The `Is<A,B>` Leibniz equality witness for GADT simulation
- The Phase GAT for symbolic/concrete separation

---

## Section 7: The Opacity Guarantee

**Claim (Eventual Detection).** If the SUT returns a "wrong" handle at step k (passing the opaque bridge), then any behavioral difference manifests at some step k + j when the handle is used with a transparent bridge.

This is the key insight about why `Opaque` is safe: wrong handles are detected behaviorally, not immediately. The bounded bisimulation captures this.

*This claim is stated but not proved in the current formalization.*

---

## Section 8: Discussion and Limitations

- The formalization gap: the runner's operational behavior is not modeled in Lean
- Preconditions weaken the universal quantifier
- The concurrent module (crash-absence, linearizability, DPOR) exists but is not part of the pearl
- The probabilistic guarantee (how many test cases suffice) is not addressed

---

## Section 9: Related Work

**quickcheck-lockstep (de Vries, 2021).** The direct predecessor. Uses a `ModelValue` GADT. Our bridge algebra is more compositional.

**Logical relations (Reynolds, 1983; Pitts, 2000).** Our bridge algebra is a logical relation for the polynomial type language. The connection is novel in the context of test oracle specification.

**Model-based testing (Tretmans, 2008; Claessen & Hughes, 2000).** QuickCheck's state machine testing provides the operational framework. Our contribution is the bridge algebra for type-safe comparison.

**Bisimulation (Milner, 1989; Sangiorgi, 2011).** Our bounded bisimulation is standard. The connection to lockstep testing is the key claim.

**Linearizability checking (Herlihy & Wing, 1990; Wing & Gong, 1993).** The concurrent module implements linearizability checking with DPOR. Engineering, not pearl material, but positions the library uniquely.

---

## Key Sentences for the Pearl

These are the sentences that make or break the paper:

**The hook:** "Property-based testing of stateful systems has a type problem: the system-under-test returns file handles, but the model returns integers."

**The insight:** "We observe that the comparison specification is a *logical relation* -- a type-indexed family of relations preserved by type constructors -- and that the fundamental theorem gives us compositionality for free."

**The bridge definition:** "A *bridge* between types R and M is a span R <- O -> M with decidable equality at the apex."

**The opacity story:** "An opaque bridge is the trivial relation Top: it relates everything now, but a wrong handle will be caught later when it *behaves* differently."

**The bisimulation connection:** "A passing lockstep test at depth n is a constructive witness of the bounded bisimulation at depth n."

**The punchline:** "Bridges are the `deriving Eq` of cross-type comparison: they follow the structure of the type, and the correctness proof follows the structure of the bridge."

---

## Alternative: Tool Paper Structure (ESOP/ECOOP or ISSTA/ASE)

### Title
**proptest-lockstep: Stateful Property Testing with Composable Bridges, Linearizability Checking, and Machine-Checked Soundness**

### Structure

1. **Introduction** -- the problem of testing stateful APIs with opaque handles
2. **The Bridge Algebra** -- composable observation (condensed from the pearl)
3. **The Projection Language** -- GVar/Op for compound return types
4. **The Runner** -- Phase GAT, proc macro, self-contained execution
5. **Concurrent Testing** -- crash-absence, linearizability, DPOR, ConflictMaximizing, loom
6. **Formal Verification** -- Lean 4 formalization (24 theorems, zero sorry)
7. **Evaluation** -- (needs to be added)
   - Bug-finding study on N real Rust crates
   - DPOR pruning effectiveness
   - ConflictMaximizing vs. RoundRobin bug-finding rates
   - Lines of boilerplate saved by proc macro
   - Lean proof effort
8. **Related Work** -- expanded to cover Jepsen, PROPER, Shuttle, loom, TLA+
9. **Conclusion**
