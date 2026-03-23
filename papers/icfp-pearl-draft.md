# Bridges as Logical Relations: Datatype-Generic Testing with Machine-Checked Metatheory

## ICFP Functional Pearl — Draft Outline & Introduction

### The One Idea

Bridge derivation is generic programming over logical relations. Just as `deriving Eq` gives structural equality, `#[derive(LockstepBridge)]` gives structural observation — a type-indexed family of decidable equivalences preserved by type constructors.

---

## Outline

### 1. Opening: The Testing Oracle Problem (~2 pages)

*Hook:* Property-based testing of stateful systems requires an oracle — a way to compare what the system-under-test (SUT) produced against what the model predicted. When the types match perfectly (an integer counter), the oracle is just equality. When they don't (the SUT returns an opaque handle, the model returns an ID), the tester needs something more nuanced: a *bridge* that relates the two types through a common observation.

*The puzzle:* How do you build these bridges compositionally? If a function returns `Result<(Handle, usize), Error>`, the bridge must decompose into: a `Result` bridge wrapping an `Ok` bridge (which is a tuple bridge of an opaque bridge and a transparent bridge) and an `Err` bridge. And crucially: the *precision* of the bridge determines the *strength* of the test. A fully opaque bridge tests nothing; a fully transparent bridge tests everything. The space between is where interesting testing lives.

*The reveal:* These bridges are logical relations. The compositional structure is the fundamental theorem of logical relations (preservation by type constructors). The precision ordering is inclusion of relations. And the whole thing can be derived mechanically from the type structure — because the type constructors are polynomial functors, and logical relations over polynomial functors are themselves polynomial.

*Contributions:*
- We identify the bridge algebra in lockstep property-based testing as a logical relation, factored through a decidable observation type (Section 2)
- We show that bridge derivation is datatype-generic programming: the polynomial functor structure of types determines the bridge (Section 3)
- We prove that bridge refinement (the precision ordering) is induced by structural refinement of polynomial shapes, via a natural transformation (Section 4)
- We connect bridge-indexed bisimulation to observational refinement and game semantics, giving three equivalent characterizations of what a passing test proves (Section 5)
- All 376 definitions are machine-checked in Lean 4 with zero sorry (Section 6)

### 2. Bridges as Logical Relations (~3 pages)

*Start concrete:* Show a simple lockstep test (KV store). The model returns a value, the SUT returns the same value. The bridge is `Transparent<V>` — just check equality.

*Complicate:* File system example. The model returns a `FileId` (integer), the SUT returns a `FileHandle` (opaque). Can't check equality. Bridge is `Opaque<FileHandle, FileId>` — ignore the difference. But now: a function returns `Result<FileHandle, IoError>`. The bridge is `ResultBridge<Opaque<..>, Transparent<IoError>>`. Composition!

*Formalize:* Define `Bridge R M` with the observation factoring. State `bridge_equiv`. Show the primitive bridges: `transparent` (identity observation), `opaque` (unit observation). Show the lifts: `sumBridge`, `prodBridge`, `optionBridge`, `listBridge`.

*The fundamental theorem:* Each lift preserves bridge equivalence. If the components are related, the composite is related. This IS the fundamental theorem of logical relations, specialized to our observation-factored setting.

*Key definition:*
```
Bridge R M := { Observed : Type,
                observe_real : R → Observed,
                observe_model : M → Observed,
                dec_eq : DecidableEq Observed }
```

### 3. Polynomial Derivation (~3 pages)

*The shape of a bridge:* Define `BridgeShape` — the grammar of polynomial functors (atom, unit, sum, prod, option, list). Show that every bridge constructor corresponds to a shape constructor.

*The derivation algorithm:* Given two Rust types (the SUT return type and the model return type), the proc macro:
1. Parses both types into polynomial shape trees
2. Aligns them structurally
3. At each leaf: if the types match, use `transparent`; if they differ, use `opaque`
4. Lifts compose the bridges bottom-up

*Why this is generic programming:* The derivation IS structural recursion on the polynomial shape. `deriving Eq` does the same thing for equality. `deriving Bridge` does it for logical relations.

*The Lean formalization:*
- `BridgeShape.Obs` — the polynomial functor
- `BridgeShape.fmap` with both functor laws (`fmap_id`, `fmap_comp`)
- `shapeBridge` — construct a bridge from a shape + observations
- `shape_bridge_equiv` — the fundamental connection

### 4. Refinement as Natural Transformation (~2 pages)

*The precision spectrum:* `Transparent` (finest, strongest test) at top. `Opaque` (coarsest, weakest test) at bottom. Everything else is in between.

*Structural refinement:* `ShapeRefines` — when one shape is finer than another (has `atom` where the other has `unit`). The coarsening map `ShapeRefines.coarsen` transforms finer observations into coarser ones.

*The connection theorem:* `shape_refines_bridge_refines` — structural refinement induces bridge refinement. Finer shapes give finer bridges give stronger bisimulation guarantees.

*Naturality:* `coarsen_natural` — the coarsening map commutes with the polynomial functor's action on morphisms. This is a natural transformation between polynomial functors, making the refinement ordering categorical.

*Practical consequence:* The `refines_strengthen_bisim` theorem says: replacing any bridge with a finer one strictly strengthens the testing guarantee. The user can start with all-opaque (fast, weak) and incrementally refine (slower, stronger).

### 5. What a Passing Test Proves (~3 pages)

*Three equivalent characterizations:*

1. **Logical:** `bounded_bisim n sm ss` — at every depth up to n, every action produces bridge-equivalent results and the successor states remain in the bisimulation. (`Lockstep.lean`)

2. **Observational:** `observational_refinement_equiv` — the SUT and model produce identical bridge observations on all traces up to length n. (`ObservationalRefinement.lean`)

3. **Game-semantic:** `bisim_game_semantic` — the Attacker (who tries to distinguish the systems) has no winning strategy of depth ≤ n. The witness IS the minimal failing test case. (`GameSemantics.lean`)

*The runner correspondence:* `runner_bounded_bisim_equiv` — the test runner checking bridge equivalence at each step IS the bisimulation check. Passing all traces ↔ bounded bisimulation. This is a biconditional — no gap between testing and the formal property.

*Compositional testing:* `product_bisim_iff` — the product of two independently-tested subsystems satisfies bisimulation iff both components do. Test each subsystem separately; compose the guarantees.

### 6. Mechanization (~1 page)

*Statistics:* 376 definitions, 33 Lean 4 files, zero sorry. 12 rounds of adversarial review.

*What's formalized:* Bridge algebra, bounded bisimulation, runner correspondence (biconditional), observational refinement (biconditional), game-semantic characterization (biconditional), polynomial functor laws, shape refinement, naturality of coarsening, compositional bisimulation with associativity, DPOR swap soundness, sleep set equivalence, crash-recovery bisimulation, session consistency with monotonic reads, crash-session composition with history reset, crash-transparent action elimination.

*What's NOT formalized:* The Rust implementation itself (specification verification, not code verification). The Rust-Lean gap is bridged by shared structure, not formal proof. Honestly documented.

### 7. Related Work (~1.5 pages)

- **Logical relations** (Reynolds 1983, Pitts 2000): We instantiate the logical relation framework with observation-factored decidable equivalences. The novelty is the polynomial derivation and the connection to testing.
- **Generic programming** (Hinze, Gibbons, Magalhães): We apply datatype-generic techniques to logical relations rather than equality or serialization.
- **quickcheck-lockstep** (de Vries): The Haskell original. We add: formal metatheory, polynomial derivation, crash recovery, session consistency, DPOR, game semantics.
- **Iris / RustBelt** (Jung et al.): Full program verification using logical relations. We're lighter-weight (testing, not verification) but have machine-checked metatheory of the testing framework itself.
- **QuickCheck / Hedgehog / proptest**: PBT frameworks without formal metatheory. We provide the first machine-checked soundness proofs for this style of testing.

### 8. Conclusion (~0.5 pages)

Bridges are logical relations. The polynomial functor structure makes them derivable. The refinement ordering makes them tunable. The game-semantic characterization makes failures concrete. And all of this is machine-checked.

---

## Draft Introduction

Property-based testing of stateful systems requires an *oracle*: given the system-under-test's response and the model's prediction, are they "the same"? When both return an integer, the answer is equality. But stateful systems routinely return opaque handles, internal identifiers, or values whose representation differs between the implementation and its specification. The tester needs something more flexible than equality — a *bridge* that relates two potentially different types through a common notion of observation.

Consider a file system test. The model predicts that opening a file returns `FileId(3)`. The SUT returns `FileHandle(0x7f3a...)`. These cannot be compared directly. Instead, the tester records both values and checks that *future operations* using either value produce consistent results. The bridge between `FileHandle` and `FileId` is *opaque*: it accepts any pair, but defers judgment to later actions that use the handle through a *transparent* bridge (like comparing read contents).

Now consider a function that returns `Result<(FileHandle, usize), IoError>`. The bridge must decompose: the `Ok` variant uses a tuple bridge (opaque for the handle, transparent for the byte count), while the `Err` variant uses a transparent bridge. This composition is not ad hoc — it follows the structure of the return type.

In this pearl, we show that this compositional structure is an instance of a well-known concept: *logical relations* (Reynolds, 1983). A bridge is a type-indexed family of decidable equivalences, preserved by type constructors — exactly a logical relation, factored through a common observation type. The type constructors (sum, product, option, list) are polynomial functors, and the bridge lifts are the fundamental theorem of logical relations applied to each functor.

This identification has three consequences:

1. **Derivation.** Because bridges follow the polynomial structure of types, they can be derived mechanically. Our Rust proc macro `#[derive(LockstepBridge)]` reads the type structure and generates the bridge by structural recursion — the same technique as `deriving Eq` in Haskell, but for logical relations instead of equality.

2. **Refinement.** Bridges form a lattice under inclusion. Transparent (identity observation) is the finest; opaque (unit observation) is the coarsest. Replacing any bridge with a finer one strictly strengthens the testing guarantee. The lattice structure is induced by a natural transformation between polynomial functors.

3. **Characterization.** A passing lockstep test at depth *n* establishes a bounded bisimulation — and we prove three equivalent characterizations: as a recursive predicate, as observational indistinguishability on all traces, and as the absence of an Attacker's winning strategy in a bisimulation game. The game-semantic witness IS the minimal failing test case.

All 376 definitions are machine-checked in Lean 4 with zero `sorry`. The formalization covers the bridge algebra, bisimulation theory, runner correspondence (biconditional), observational refinement (biconditional), game-semantic characterization (biconditional), polynomial functor laws, compositional testing with associativity, DPOR soundness, crash-recovery bisimulation, and session consistency — the most comprehensive formal metatheory of any property-based testing framework.

This paper makes the following contributions:

- We identify bridge algebras as logical relations factored through decidable observation types, and show the compositional structure is the fundamental theorem of logical relations (§2).
- We show that bridge derivation is datatype-generic programming over polynomial functors, and that the Rust proc macro implements structural recursion on type shapes (§3).
- We prove that structural refinement of polynomial shapes induces bridge refinement via a natural transformation, giving a categorical foundation for the precision spectrum (§4).
- We connect bridge-indexed bisimulation to three equivalent characterizations — logical, observational, and game-semantic — each proved as a machine-checked biconditional (§5).
- We provide the most comprehensive mechanized metatheory of property-based testing: 376 definitions in Lean 4, zero sorry, surviving 12 rounds of adversarial review (§6).
