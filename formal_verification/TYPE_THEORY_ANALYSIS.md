# Type-Theoretic Analysis of proptest-lockstep

A type-theoretic framing of the bridge algebra and its connections to established type theory, intended as reference material for the ICFP pearl.

## The Bridge Algebra Through the Lens of Type Theory

### What the Bridge Is (Formally)

The `Bridge R M` structure is a **binary logical relation** in the sense of Reynolds (1983), but with a specific computational structure that makes it more than an abstract relation:

```
Bridge R M := { Observed : Type,
                observe_real : R → Observed,
                observe_model : M → Observed,
                dec_eq : DecidableEq Observed }
```

This is a **span** in the category of types. Two types `R` and `M` are related by projecting them both into a common observation space, then checking equality there. This is fundamentally different from a relational logical relation `R → M → Prop` — this version **factors** the relation through a decidable equality on observations.

## Connection 1: Bridges as Galois Connections (Refinement Types)

The refinement ordering `bridge_refines b1 b2 := ∀ r m, bridge_equiv b1 r m → bridge_equiv b2 r m` is the inclusion ordering on logical relations. Because bridges factor through observation types, this has a concrete computational meaning:

```
b1 refines b2  ⟺  ∃ f : b1.Observed → b2.Observed,
                    f ∘ b1.observe_real = b2.observe_real ∧
                    f ∘ b1.observe_model = b2.observe_model
```

This is `ShapeRefines.coarsen`. The coarsening map IS the morphism in the category of spans that witnesses refinement. In refinement type terms: a finer bridge is a more precise abstract interpretation of the real/model relationship.

## Connection 2: Polynomial Functors and Generic Programming

`BridgeShape` is a **polynomial functor** in the sense of Gambino-Kock and Spivak:

```
⟦atom⟧(X) = X                         -- identity functor
⟦unit⟧(X) = 1                          -- constant functor
⟦sum s t⟧(X) = ⟦s⟧(X) + ⟦t⟧(X)       -- coproduct
⟦prod s t⟧(X) = ⟦s⟧(X) × ⟦t⟧(X)     -- product
⟦option s⟧(X) = 1 + ⟦s⟧(X)           -- Maybe
⟦list s⟧(X) = μL. 1 + ⟦s⟧(X) × L    -- free monoid
```

In type theory, these are the **strictly positive functors** — exactly the functors for which inductive types can be defined. The proc macro `#[derive(LockstepBridge)]` is doing **datatype-generic programming**: it reads the polynomial structure of a Rust type and derives the corresponding bridge by structural recursion on the type's shape.

**The pearl story: bridge derivation IS generic programming over logical relations.** Just as Haskell's `deriving Eq` generically derives equality by the polynomial structure of a datatype, the macro generically derives the observation function.

### Proved properties:
- `fmap_id`: the polynomial functor preserves identity
- `fmap_comp`: the polynomial functor preserves composition
- `coarsen_natural`: coarsening is a natural transformation between polynomial functors
- `shape_refines_bridge_refines`: structural refinement on shapes induces bridge refinement

## Connection 3: Game Semantics and the Curry-Howard Correspondence

`bisim_game_semantic` — `¬bounded_bisim ↔ ∃ BisimWitness` — has a precise type-theoretic interpretation through the Curry-Howard correspondence:

- `bounded_bisim n sm ss` is a **proposition** (in Lean's `Prop`)
- `BisimWitness` is a **type** (in Lean's `Type`)
- The forward direction extracts a **computational witness** from a classical proof of non-bisimulation
- The backward direction is a **constructive refutation**: given a witness, produce `False`

In game-semantic terms (Abramsky-Jagadeesan-Malacaria): the Attacker's strategy IS a term of type `BisimWitness`, and the Defender's winning condition IS `bounded_bisim`. The biconditional proves that these two views — the constructive witness and the universal property — coincide at every finite depth.

This connects to **realizability theory**: the witness is a realizer for the negation of bisimulation. The classical direction (using `Classical.byContradiction`) is where computational content is lost — existence without computable extraction. The constructive direction preserves computational content completely.

### The crash extension:
`crash_bisim_game_semantic` extends this to crash-recovery systems with four Attacker moves (bridge_fail, invariant_fail, deeper, crash_then). The forward direction requires decidability of both bridge equivalence AND the state invariant.

## Connection 4: Session Types and Session Consistency

`session_bisim` threading per-session histories through the bisimulation is structurally similar to **session types** (Honda, 1993). In session type theory:

- A session is a typed communication channel
- Each message advances the session type (state machine)
- Session fidelity = the channel behaves according to its type

The proptest-lockstep model:
- A session is a client's interaction history
- Each write/read advances the session history
- Session consistency (RYW) = the history satisfies the ordering guarantee

`apply_session_write_commute` — that history updates at different sessions commute — is the PBT analog of **session type independence**: independent sessions don't interfere. In multiparty session type theory (Honda-Yoshida-Carbone), this would be a global type projection property.

## Connection 5: Decidable Equality and Constructive Type Theory

The `dec_eq : DecidableEq Observed` field on `Bridge` is not an afterthought — it is the **constructive content** that makes the logical relation computable. In Martin-Lof type theory terms:

- `bridge_equiv b r m : Prop` is a proposition (proof-irrelevant)
- `bridge_equiv_decidable b r m : Decidable (bridge_equiv b r m)` is a decision procedure (computationally relevant)

This is precisely the gap between a logical relation (which exists in the metatheory) and a testing oracle (which must be executable). The `dec_eq` field bridges this gap: it makes the Lean `Prop`-level proofs correspond to the Rust `check_bridge` computation that returns `Result<(), String>`.

## What This Means for the ICFP Pearl

The pearl should frame bridges as living at the intersection of three established type-theoretic concepts:

1. **Logical relations** (Reynolds) — bridges ARE logical relations, with the specific computational structure of factoring through observation
2. **Polynomial functors** (generic programming) — bridge derivation IS datatype-generic programming over the polynomial structure of types
3. **Decidable equality** (constructive type theory) — the `dec_eq` field makes bridge equivalence computable, connecting the Lean `Prop` world to the Rust `check_bridge` computation

## Suggested Paper Title

*"Bridges as Logical Relations: Datatype-Generic Testing with Machine-Checked Metatheory"*

## Suggested Hook

"We show that the observation functions used in lockstep property-based testing form a logical relation — a type-indexed family of decidable equivalences preserved by type constructors. The polynomial functor structure makes derivation mechanizable, the refinement ordering makes precision tunable, and the game-semantic characterization makes failures concrete. All 376 definitions are machine-checked in Lean 4 with zero sorry."

## References

- Reynolds, J.C. (1983). "Types, Abstraction and Parametric Polymorphism"
- Gambino, N. & Kock, J. (2013). "Polynomial functors and polynomial monads"
- Spivak, D.I. (2020). "Polynomial Functors: A General Theory of Interaction"
- Abramsky, S., Jagadeesan, R., & Malacaria, P. (2000). "Full Abstraction for PCF" (game semantics)
- Honda, K. (1993). "Types for Dyadic Interaction" (session types)
- Honda, K., Yoshida, N., & Carbone, M. (2008). "Multiparty Asynchronous Session Types"
- Milner, R. (1989). "Communication and Concurrency" (bisimulation)
- de Vries, E. "quickcheck-lockstep" (the Haskell original)
