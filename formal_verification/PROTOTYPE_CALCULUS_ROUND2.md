# lambda-bridge Revised: Accounting for the Formalization

## Status of the Original Calculus

The original lambda-bridge calculus (PROTOTYPE_CALCULUS.md) identified Theorem 5 (Runner Soundness) as "the theorem the Lean formalization should prove." That theorem is now proved — as `runner_bounded_bisim_equiv`, a full biconditional. The formalization has also gone far beyond what the original calculus anticipated, proving DPOR soundness, linearizability, observational refinement, testing completeness, bridge refinement, and derived bridge preservation.

This document assesses which parts of lambda-bridge need updating and proposes extensions for the new results.

## Question 1: Does lambda-bridge Need Updating?

**Yes, substantially.** The original calculus is correct but incomplete:

| Original Element | Status | Notes |
|---|---|---|
| Bridge formation rules (B-Trans, B-Opaque, B-Sum, etc.) | ✅ Correct | Match Bridge.lean exactly |
| Observation typing (T-ObsR, T-ObsM) | ✅ Correct | |
| Bridge equivalence definition | ✅ Correct | `bridge_equiv` in Lean |
| Projection typing (P-Id through P-Comp) | ✅ Correct | Not formalized in Lean (TypedEnv gap) |
| Phase-indexed typing (T-SymVar, T-ConVar) | ✅ Correct | Not formalized in Lean |
| Runner judgment (R-Empty, R-Step) | ✅ Correct | Now proved as `runner_passes` in Lean |
| Theorem 5 (Runner Soundness) | ✅ Now proved | `runner_bounded_bisim_equiv` (biconditional!) |
| Theorem 8 (Opaque Detection) | ✅ Now proved | `opaque_step_then_detect`, `opaque_depth_sensitivity` |
| Bounded bisimulation definition | ✅ Correct | `bounded_bisim` in Lean |

**What's missing from the original calculus:**
- No notion of bridge refinement or ordering
- No concurrency primitives (DPOR, linearizability)
- No precondition filtering
- No observational refinement theorem
- No testing completeness
- No bridge derivation formalization

## Question 2: Typing Rules for Observational Refinement

The `observational_refinement_equiv` theorem establishes:

```
bounded_bisim n sm ss  ↔  ∀ pre a. |pre| + 1 ≤ n → obs_sut(a, run(pre, ss)) = obs_model(a, run(pre, sm))
```

This is a semantic property, not a typing rule. But we can express it as a **judgment**:

### Observational Refinement Judgment

```
sm ≈_n ss   <=>   ∀ pre : Act*, a : Act. |pre| + 1 ≤ n →
                    observe_R(bridge(a), stepS(a, runS(pre, ss)).2)
                  = observe_M(bridge(a), stepM(a, runM(pre, sm)).2)
```

Where `runS` and `runM` fold `stepS`/`stepM` over a prefix:

```
runS([], ss) = ss
runS(a :: as, ss) = runS(as, stepS(a, ss).1)
```

### The Equivalence Rule

```
     bisim(Sys, n, sm, ss)
     ---------------------- [Bisim-to-ObsRef]
         sm ≈_n ss

     sm ≈_n ss
     ---------------------- [ObsRef-to-Bisim]
         bisim(Sys, n, sm, ss)
```

These correspond to the two directions of `observational_refinement_equiv`.

### Testing Completeness Rule

```
     observe_R(bridge(a), stepS(a, runS(pre, ss)).2)
       ≠ observe_M(bridge(a), stepM(a, runM(pre, sm)).2)
     -------------------------------------------------------- [Bug-Detection]
                ¬ bisim(Sys, |pre| + 1, sm, ss)
```

This is `testing_completeness`. The contrapositive of [Bisim-to-ObsRef].

### Bug Localization Rule

```
     ¬ bisim(Sys, n+1, sm, ss)
     -------------------------------------------- [Bug-Localize]
     ∃ a. ¬(stepS(a,ss).2 ~_{bridge(a)} stepM(a,sm).2)
        ∨ ¬ bisim(Sys, n, stepM(a,sm).1, stepS(a,ss).1)
```

This is `bug_localization`. Note: the original calculus had no rule for *failure analysis*.


## Question 3: Polynomial Derivation in the Calculus

### Bridge Derivation as a Meta-function

Add a **derivation judgment** to the calculus:

```
tau_R ~ tau_M |- Omega ⊢ beta
```

Read: "Given real type `tau_R`, model type `tau_M`, and opaque map `Omega`, derive bridge `beta`."

### Derivation Rules

```
                          ------------------- [D-Same]
                          tau ~ tau |- Omega ⊢ Delta(tau)


     (R, M) in Omega
     ------------------- [D-Opaque]
     R ~ M |- Omega ⊢ Top(R, M)


     tau_1R ~ tau_1M |- Omega ⊢ beta_1    tau_2R ~ tau_2M |- Omega ⊢ beta_2
     ----------------------------------------------------------------------- [D-Sum]
     tau_1R + tau_2R ~ tau_1M + tau_2M |- Omega ⊢ beta_1 + beta_2


     tau_1R ~ tau_1M |- Omega ⊢ beta_1    tau_2R ~ tau_2M |- Omega ⊢ beta_2
     ----------------------------------------------------------------------- [D-Prod]
     tau_1R x tau_2R ~ tau_1M x tau_2M |- Omega ⊢ beta_1 x beta_2


     tau_R ~ tau_M |- Omega ⊢ beta
     ------------------------------- [D-Opt]
     tau_R? ~ tau_M? |- Omega ⊢ beta?


     tau_R ~ tau_M |- Omega ⊢ beta
     ------------------------------- [D-List]
     [tau_R] ~ [tau_M] |- Omega ⊢ [beta]


                          ------------------- [D-Unit]
                          () ~ () |- Omega ⊢ UnitBridge
```

### Derivation Soundness Theorem

```
If  tau_R ~ tau_M |- Omega ⊢ beta
Then  Real(beta) = tau_R  and  Model(beta) = tau_M  and  |- beta bridge
```

This says derived bridges are well-formed and have the right types. The preservation theorems (from `DerivedBridge.lean`) then guarantee bridge_equiv is preserved by the derivation.

### Derivation Monotonicity

```
If  tau_R ~ tau_M |- Omega ⊢ beta
and tau_R ~ tau_M |- Omega' ⊢ beta'
and Omega ⊆ Omega'  (more types are opaque)
Then  beta refines beta'  (finer bridge → stronger guarantee)
```

This captures `derivation_monotone_*`: adding opaque entries coarsens the bridge.


## Question 4: Concurrency Primitives for DPOR/Linearizability

### Concurrent Execution Judgment

Extend the calculus with a concurrent execution model:

```
-- Concurrent branches
b ::= branch(as)                    -- a branch is a list of actions
B ::= [b_1, ..., b_k]               -- k concurrent branches

-- An interleaving (linearization)
L ::= [a_1, ..., a_n]               -- a permutation preserving within-branch order

-- Recorded operation
rec ::= (a, v_sut)                  -- action paired with its SUT result
```

### Linearization Check Judgment

```
     sm |- [] ⊢ ok                                        [Lin-Empty]

     stepM(a, sm) = (sm', rm)
     rm ~_{bridge(a)} v_sut
     sm' |- recs ⊢ ok
     ----------------------------------- [Lin-Step]
     sm |- (a, v_sut) :: recs ⊢ ok
```

This is `linearization_check` from DPOR.lean.

### Linearizability Judgment

```
     L is a permutation of flatten(B)
     L preserves within-branch order
     sm |- L ⊢ ok
     ----------------------------------- [Linearizable]
     sm |- B linearizable
```

This is `is_linearizable` from Linearizability.lean.

### Commutativity Judgment

```
     stepM(b, stepM(a, sm).1).1 = stepM(a, stepM(b, sm).1).1
     stepM(a, sm).2 = stepM(a, stepM(b, sm).1).2
     stepM(b, stepM(a, sm).1).2 = stepM(b, sm).2
     ------------------------------------------------- [Commute]
     a ⋈_{sm} b
```

This is `model_commute` from DPOR.lean.

### DPOR Swap Rule

```
     sm |- r1 :: r2 :: recs ⊢ ok
     r1.action ⋈_{sm} r2.action
     -------------------------------------- [DPOR-Swap]
     sm |- r2 :: r1 :: recs ⊢ ok
```

This is `dpor_swap_sound`. The biconditional `dpor_swap_iff` says the rule works in both directions.

### DPOR Swap at Position

```
     sm |- pre ++ r1 :: r2 :: suf ⊢ ok
     r1.action ⋈_{runM(pre, sm)} r2.action
     ---------------------------------------- [DPOR-Swap-At]
     sm |- pre ++ r2 :: r1 :: suf ⊢ ok
```

This is `dpor_swap_at`.


## Question 5: Bridge Refinement vs. Subtyping

### The Relationship

`bridge_refines b1 b2` says: every pair related by `b1` is also related by `b2`. In subtyping terms:

```
b1 <: b2   <=>   ∀ r m. r ~_{b1} m → r ~_{b2} m
```

This is **covariant** subtyping on the *relation* — a finer bridge (stronger relation) is a subtype of a coarser one. This is analogous to:
- **Behavioral subtyping** (Liskov): if T1 <: T2, every context expecting T2 works with T1
- **Refinement types**: {x : T | P(x)} <: T — the refined type is a subtype

### Subsumption Rule

Add a subsumption rule to the calculus:

```
     |- beta_1 bridge    |- beta_2 bridge    beta_1 <: beta_2
     Gamma |- e_R : Real(beta_1)    Gamma |- e_M : Model(beta_1)
     e_R ~_{beta_1} e_M
     ------------------------------------------------------------ [Sub-Bridge]
     e_R ~_{beta_2} e_M
```

This says: if values are related by a finer bridge, they're related by any coarser bridge. This corresponds to `bridge_refines` applied at the value level.

### Bisimulation Subsumption

```
     bisim(Sys, n, sm, ss)    bridge'(a) <: bridge(a) for all a
     ------------------------------------------------------------ [Sub-Bisim]
     bisim(Sys{bridge := bridge'}, n, sm, ss)
```

This is `refines_strengthen_bisim` — replacing bridges with finer ones preserves bisimulation.

### Why It's Not Standard Subtyping

Standard subtyping is on *types*: `T1 <: T2` means values of type `T1` can be used where `T2` is expected. Bridge refinement is on *relations between types*: `b1 <: b2` means the relation `b1` induces is contained in the relation `b2` induces.

The bridge ordering is more like a **graded modality**: `Transparent` is the "most informative" mode, `Opaque` is the "least informative" mode, and the ordering captures information loss. This connects to coeffect systems (Petricek et al.) where the ordering tracks how much context information a computation uses.

### Lattice Extension (Speculative)

To make it a lattice, define:

```
-- Meet: finest bridge coarser than both
beta_1 ∧ beta_2 : Bridge R M
  where Obs(beta_1 ∧ beta_2) = Obs(beta_1) × Obs(beta_2)
        observe_R(beta_1 ∧ beta_2, r) = (observe_R(beta_1, r), observe_R(beta_2, r))
        observe_M(beta_1 ∧ beta_2, m) = (observe_M(beta_1, m), observe_M(beta_2, m))

-- Join: coarsest bridge finer than both
beta_1 ∨ beta_2 : Bridge R M
  where Obs(beta_1 ∨ beta_2) = Obs(beta_1) × Obs(beta_2) / ~
        where (o1, o2) ~ (o1', o2') iff
          (∃ r. observe_R(beta_1, r) = o1 ∧ observe_R(beta_2, r) = o1' ...) -- quotient by the kernel
```

The meet is straightforward (product of observations). The join requires a quotient type — this is where the lattice becomes hard to implement in Lean without `Quotient`.


## Question 6: Revised Calculus Overview

### lambda-bridge v2: Full Calculus

The revised calculus extends the original with:

1. **Bridge refinement** as subtyping (Section 5)
2. **Observational refinement** judgment and equivalence rules (Section 2)
3. **Bridge derivation** judgment with soundness (Section 3)
4. **Concurrency** — linearization, commutativity, DPOR swap (Section 4)
5. **Testing completeness** — bug detection and localization rules (Section 2)
6. **Precondition filtering** — restricted bisimulation (below)

### Preconditioned Bisimulation

```
     Pre(a, sm) = false
     --------------------------------- [PBisim-Skip]
     sm ≈^Pre_n ss  (action a is skipped)

     Pre(a, sm) = true
     stepM(a,sm) = (sm', rm)    stepS(a,ss) = (ss', rs)
     rs ~_{bridge(a)} rm    sm' ≈^Pre_n ss'
     ----------------------------------------- [PBisim-Step]
     sm ≈^Pre_{n+1} ss
```

With the conservativity rule:

```
     bisim(Sys, n, sm, ss)
     ---------------------- [Pre-Conservative]
     sm ≈^Pre_n ss
```

This is `universal_implies_preconditioned`.

### Summary of Judgments

| Judgment | Meaning | Lean Theorem |
|---|---|---|
| `⊢ beta bridge` | Bridge is well-formed | (structural) |
| `r ~_beta m` | Bridge equivalence | `bridge_equiv` |
| `beta_1 <: beta_2` | Bridge refinement | `bridge_refines` |
| `bisim(n, sm, ss)` | Bounded bisimulation | `bounded_bisim` |
| `sm ≈_n ss` | Observational refinement | `observational_refinement_equiv` |
| `sm ≈^Pre_n ss` | Preconditioned bisimulation | `precond_bisim` |
| `sm ⊢ recs ⊢ ok` | Linearization check | `linearization_check` |
| `sm ⊢ B linearizable` | Linearizability | `is_linearizable` |
| `a ⋈_sm b` | Model commutativity | `model_commute` |
| `tau_R ~ tau_M ⊢_Omega beta` | Bridge derivation | `derive_bridge` (proc macro) |
| `sm, ss ⊢ trace ▷ ok` | Runner passes | `runner_passes` |

### Key Metatheorems (All Machine-Checked)

1. **Fundamental Theorem**: Lifts preserve `~_beta` (Bridge.lean)
2. **Runner ↔ Bisim**: `sm, ss ⊢ all traces of length n ▷ ok` iff `bisim(n, sm, ss)` (Runner.lean)
3. **Bisim ↔ ObsRef**: `bisim(n, sm, ss)` iff `sm ≈_n ss` (ObservationalRefinement.lean)
4. **Completeness**: `¬(sm ≈_n ss)` implies `¬ bisim(n, sm, ss)` (TestingCompleteness.lean)
5. **DPOR Swap**: `a ⋈_sm b` implies `r1::r2::rest ⊢ ok` iff `r2::r1::rest ⊢ ok` (DPOR.lean)
6. **Monotonicity**: `bisim(m, sm, ss)` and `n ≤ m` implies `bisim(n, sm, ss)` (Lockstep.lean)
7. **Opaque Detection**: `¬ bisim(k, sm', ss')` implies `¬ bisim(k+1, sm, ss)` (OpaqueDetection.lean)
8. **Refinement Strength**: `beta' <: beta` implies `bisim` under `beta` implies `bisim` under `beta'` (BridgeRefinement.lean)
9. **Derivation Preservation**: Each derivation rule preserves `~_beta` (DerivedBridge.lean)
10. **Precondition Conservativity**: `bisim(n, sm, ss)` implies `sm ≈^Pre_n ss` (Precondition.lean)


## What the Revised Calculus Reveals

1. **The three-way equivalence `runner ↔ bisim ↔ obsref` is the central theorem.** It says that the operational semantics (runner), the denotational semantics (bisimulation), and the observational semantics (observation equality) all agree. This is the analog of "adequacy" in programming language theory.

2. **Bridge refinement is a coeffect system.** The ordering from Transparent (most information) to Opaque (least information) tracks how much observable information a test extracts. Finer bridges extract more; coarser bridges extract less. The `refines_strengthen_bisim` theorem says: extracting more information gives a stronger guarantee — the coeffect analog of "using more context yields more precise analysis."

3. **DPOR swap is a coherence condition.** Two operations commute iff swapping them preserves the linearization check. This is a coherence condition on the concurrent execution: the linearization check is independent of the order in which commuting operations are scheduled. In categorical terms, this is the diagram commuting condition for a symmetric monoidal structure on the operation space.

4. **The calculus is the internal language of the bridge category.** The bridge algebra, with its lifts and refinement ordering, forms a category. Types are objects, bridges are morphisms (spans), lifts are functors, and refinement is the ordering on hom-sets. lambda-bridge is the internal language of this category — programs in the calculus correspond to morphisms in the bridge category, and typing ensures the bridge structure is preserved.
