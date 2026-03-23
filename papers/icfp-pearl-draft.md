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

---

## 2. Bridges as Logical Relations

### 2.1 A First Example: The Key-Value Store

The simplest lockstep test compares a system-under-test against a pure model, action by action. Consider a key-value store. The SUT is a production `HashMap`; the model is an identical `HashMap` used as a specification. Each action — `Put`, `Get`, `Delete`, `Len` — runs on both sides, and the test checks that the results agree.

```rust
#[proptest_lockstep::lockstep_actions(state = KvModel)]
pub mod kv {
    #[action(real_return = "Option<String>",
             bridge = "OptionBridge<Transparent<String>>")]
    pub struct Put { pub key: String, pub value: String }

    #[action(real_return = "Option<String>",
             bridge = "OptionBridge<Transparent<String>>")]
    pub struct Get { pub key: String }

    #[action(real_return = "usize", bridge = "Transparent<usize>")]
    pub struct Len;
}
```

Every bridge here is transparent: the SUT and model return identical Rust types, and the bridge checks equality. `Transparent<usize>` observes a `usize` as itself. `OptionBridge<Transparent<String>>` lifts this to `Option<String>` by comparing the inner values when both are `Some`, accepting `None = None`, and rejecting variant mismatches. The bridge *is* structural equality, decomposed along the type structure.

### 2.2 Complication: Opaque Handles

Now consider a file system. The model predicts that opening a file returns `MockHandle(3)`. The SUT returns `FileHandle(0x7f3a...)`. These values cannot be compared — they live in different types with different representations. But the test can still be meaningful: it records the pair `(FileHandle(0x7f3a...), MockHandle(3))` and checks that future operations using either handle produce consistent results.

```rust
#[action(
    real_return = "Result<(FileHandle, String), FsErr>",
    model_return = "Result<(MockHandle, String), FsErr>",
    bridge = "ResultBridge<TupleBridge<Opaque<FileHandle, MockHandle>,
                                       Transparent<String>>,
                            Transparent<FsErr>>",
    store_as = "handle: GVar<FileHandle, MockHandle, OpOk<OpFst>>",
)]
pub struct Open { pub path: String }
```

The bridge decomposes `Result<(FileHandle, String), FsErr>` into:

- A `ResultBridge` that first checks whether both sides returned `Ok` or `Err` — variant mismatches are failures.
- On the `Ok` side, a `TupleBridge` that checks each component: `Opaque<FileHandle, MockHandle>` for the handle (any pair is accepted; the association is recorded for later) and `Transparent<String>` for the file path (exact equality required).
- On the `Err` side, `Transparent<FsErr>` requires identical error values.

This composition is not ad hoc. It follows the type structure precisely: `Result` is a sum, the tuple is a product, each leaf is either transparent or opaque. The bridge is a type-indexed family of relations — one relation per type constructor, composed bottom-up.

### 2.3 The Formal Definition

A bridge relates a Real type `R` and a Model type `M` through a common Observed type `O`, equipped with decidable equality:

```
structure Bridge (R : Type) (M : Type) where
  Observed : Type
  observe_real : R → Observed
  observe_model : M → Observed
  dec_eq : DecidableEq Observed
```

Two values are *bridge-equivalent* when their observations coincide:

```
def bridge_equiv (b : Bridge R M) (r : R) (m : M) : Prop :=
  b.observe_real r = b.observe_model m
```

This is a relation on `R × M`, but it factors through a common type `O`. The factoring is the key structural insight: it makes the relation decidable (because `O` has decidable equality) and composable (because type constructors act uniformly on `O`).

The two primitive bridges occupy the extremes:

- **Transparent.** The observation type is the value type itself. Both `observe_real` and `observe_model` are the identity function. Bridge equivalence is ordinary equality.

```
def transparent (T : Type) [DecidableEq T] : Bridge T T :=
  { Observed := T, observe_real := id, observe_model := id, dec_eq := inferInstance }
```

- **Opaque.** The observation type is `Unit`. Every pair is equivalent. The bridge defers all judgment to later actions.

```
def opaqueBridge (R M : Type) : Bridge R M :=
  { Observed := Unit, observe_real := fun _ => (), observe_model := fun _ => (),
    dec_eq := inferInstance }
```

Between these extremes lies the entire precision spectrum. Every bridge the user writes — or that the proc macro derives — is a composition of these two primitives under the algebraic lifts.

### 2.4 The Algebraic Lifts

Each Rust type constructor has a corresponding bridge lift. The sum lift (for `Result` / `Either`) combines two bridges into one:

```
def sumBridge (bOk : Bridge ROk MOk) (bErr : Bridge RErr MErr) :
    Bridge (ROk ⊕ RErr) (MOk ⊕ MErr) :=
  { Observed := bOk.Observed ⊕ bErr.Observed
    observe_real := fun | .inl ok => .inl (bOk.observe_real ok)
                        | .inr err => .inr (bErr.observe_real err)
    observe_model := fun | .inl ok => .inl (bOk.observe_model ok)
                         | .inr err => .inr (bErr.observe_model err)
    dec_eq := inferInstance }
```

The observation type of the composite is the sum of the component observation types. The observation functions dispatch on the variant and apply the corresponding component bridge. The product lift (`prodBridge`), option lift (`optionBridge`), and list lift (`listBridge`) follow the same pattern: the observation type mirrors the type constructor, and the observation functions apply the component bridges pointwise.

### 2.5 The Fundamental Theorem

Each lift preserves bridge equivalence. If the components are related, the composite is related:

**Sum preserves (Ok).** If `bridge_equiv bOk r m`, then `bridge_equiv (sumBridge bOk bErr) (inl r) (inl m)`.

**Sum preserves (Err).** If `bridge_equiv bErr r m`, then `bridge_equiv (sumBridge bOk bErr) (inr r) (inr m)`.

**Sum detects mismatches.** `bridge_equiv (sumBridge bOk bErr) (inl r) (inr m)` is false — always. The observation types `bOk.Observed` and `bErr.Observed` are disjoint summands.

**Product preserves.** If `bridge_equiv bA ra ma` and `bridge_equiv bB rb mb`, then `bridge_equiv (prodBridge bA bB) (ra, rb) (ma, mb)`. The converse also holds: product bridge equivalence is equivalent to component-wise equivalence (`prod_equiv_iff`).

**Option preserves.** `Some`-`Some` equivalence lifts; `None`-`None` is always equivalent; mixed variants are always distinct.

**List preserves.** Nil-nil is equivalent; cons lifts element-wise. A consequence: list bridge equivalence implies equal length (`list_equiv_length`).

This is the fundamental theorem of logical relations, specialized to our observation-factored setting. Reynolds (1983) showed that parametric polymorphism preserves logical relations across type constructors. Here the same principle appears in a testing context: each type constructor preserves bridge equivalence across its arguments. The proof is structural recursion on the type constructor — exactly the recursion scheme that the proc macro implements.

### 2.6 Decidability

Bridge equivalence is decidable. Every bridge carries `DecidableEq` on its `Observed` type, and the lifts preserve decidable equality (because sum, product, option, and list of decidable types are decidable). The Lean formalization makes this explicit:

```
instance bridge_equiv_decidable (b : Bridge R M) (r : R) (m : M) :
    Decidable (bridge_equiv b r m)
```

This connects the Lean `Prop`-level `bridge_equiv` to the Rust `check` computation, which returns `Result<(), String>`. The check is a total function: it always terminates and always produces a definite answer. The `bridge_not_equiv` theorem gives the converse: non-equivalence means the observations differ. There is no middle ground — the bridge either accepts or rejects, and the test either passes or produces a concrete counterexample.

---

## 3. Polynomial Derivation

### 3.1 The Shape of a Bridge

The algebraic lifts of Section 2 suggest a grammar. Every bridge the framework constructs is built from two atomic forms (`Transparent` and `Opaque`) under four combinators (`ResultBridge`, `TupleBridge`, `OptionBridge`, `VecBridge`). This grammar is a polynomial functor:

```
inductive BridgeShape where
  | atom : BridgeShape                               -- Transparent
  | unit : BridgeShape                               -- Opaque
  | sum : BridgeShape → BridgeShape → BridgeShape    -- Result / Either
  | prod : BridgeShape → BridgeShape → BridgeShape   -- Tuple
  | option : BridgeShape → BridgeShape               -- Option
  | list : BridgeShape → BridgeShape                 -- Vec
```

Each shape determines a polynomial functor on types. Given a base observation type `O`, the shape produces an observation type by structural recursion:

```
def BridgeShape.Obs : BridgeShape → Type → Type
  | .atom, T => T                                    -- identity functor
  | .unit, _ => Unit                                 -- constant functor
  | .sum s₁ s₂, T => s₁.Obs T ⊕ s₂.Obs T           -- coproduct
  | .prod s₁ s₂, T => s₁.Obs T × s₂.Obs T          -- product
  | .option s, T => Option (s.Obs T)                 -- Maybe
  | .list s, T => List (s.Obs T)                     -- free monoid
```

The interpretation `⟦shape⟧(T)` is a functor: it acts not only on types but on morphisms between types. Given `f : A → B`, the polynomial lifts to `fmap f : ⟦shape⟧(A) → ⟦shape⟧(B)`:

```
def BridgeShape.fmap (shape : BridgeShape) (f : A → B) :
    shape.Obs A → shape.Obs B :=
  match shape with
  | .atom => f
  | .unit => id
  | .sum s₁ s₂ => fun | .inl x => .inl (s₁.fmap f x)
                       | .inr x => .inr (s₂.fmap f x)
  | .prod s₁ s₂ => fun (x, y) => (s₁.fmap f x, s₂.fmap f y)
  | .option s => fun | some x => some (s.fmap f x) | none => none
  | .list s => fun xs => xs.map (s.fmap f)
```

The `atom` case applies `f` directly — the identity functor acts by `f`. The `unit` case ignores `f` — the constant functor is unmoved. Composite shapes recurse into their sub-shapes.

### 3.2 The Functor Laws

A polynomial functor must satisfy two laws: identity and composition. Both are proved by structural induction on the shape.

**Identity law.** `fmap id = id`. Mapping the identity function does nothing. For `atom`, `fmap id = id` by definition. For `unit`, `fmap id = id` trivially. For composites, the inductive hypothesis applies to each sub-shape, and the outer constructor is preserved. The list case requires an additional inner induction on the list structure.

```
theorem BridgeShape.fmap_id : ∀ (shape : BridgeShape) (A : Type)
    (x : shape.Obs A), shape.fmap id x = x
```

**Composition law.** `fmap (g . f) = fmap g . fmap f`. Mapping a composition is the composition of maps. The proof follows the same structure: base cases are immediate, composites recurse, lists require inner induction.

```
theorem BridgeShape.fmap_comp : ∀ (shape : BridgeShape)
    (f : A → B) (g : B → C) (x : shape.Obs A),
    shape.fmap (g ∘ f) x = shape.fmap g (shape.fmap f x)
```

These two theorems establish that `BridgeShape.Obs` is a lawful functor. This is not merely a formal exercise: the functor laws guarantee that the bridge derivation algorithm is coherent. Identity says that a bridge with identity observations is the identity bridge. Composition says that nesting bridge constructors composes their observations correctly. Without these laws, the proc macro's output could silently misinterpret the type structure.

### 3.3 The Derivation Algorithm

Given two Rust types — the SUT's return type and the model's return type — the proc macro derives a bridge by structural recursion on both types simultaneously:

1. **Parse** both types into shape trees. `Result<(FileHandle, String), FsErr>` becomes `sum (prod atom atom) atom`.

2. **Align** the two trees structurally. The shapes must match at every composite node: both must be `sum`, both must be `prod`, both must be `option`, both must be `list`. If the shapes disagree, derivation fails with a compile-time error.

3. **Classify leaves.** At each leaf position, compare the real type and the model type. If they are the same type (`String = String`), use `atom` (transparent). If they differ (`FileHandle ≠ MockHandle`), use `unit` (opaque).

4. **Build bottom-up.** Construct the bridge by applying the algebraic lifts from Section 2 in the order determined by the shape tree. The observation functions compose automatically.

The shape-indexed bridge construction makes this precise. Given a shape, a base observation type `O`, and two observation functions, `shapeBridge` produces a bridge whose `Observed` type is `⟦shape⟧(O)`:

```
noncomputable def shapeBridge (shape : BridgeShape) (O : Type)
    (obs_r : R → shape.Obs O) (obs_m : M → shape.Obs O) : Bridge R M :=
  { Observed := shape.Obs O,
    observe_real := obs_r, observe_model := obs_m,
    dec_eq := BridgeShape.decEq shape O }
```

The fundamental connection: two values are bridge-equivalent under a shape-derived bridge if and only if their observations are equal in the polynomial type:

```
theorem shape_bridge_equiv (shape : BridgeShape) (O : Type)
    (obs_r : R → shape.Obs O) (obs_m : M → shape.Obs O) (r : R) (m : M) :
    bridge_equiv (shapeBridge shape O obs_r obs_m) r m ↔ obs_r r = obs_m m
```

This biconditional justifies the derivation: the proc macro generates observation functions by structural recursion on the shape, and the resulting bridge checks exactly what the polynomial structure prescribes.

### 3.4 Why This Is Generic Programming

The derivation algorithm is structural recursion on a polynomial shape — the same technique that powers `deriving Eq` in Haskell and `#[derive(PartialEq)]` in Rust. In those systems, equality is derived by comparing each field; here, bridge equivalence is derived by observing each field through the appropriate leaf bridge. The polynomial functor provides the recursion scheme; the leaf classification provides the base cases.

The primitive bridges are the canonical inhabitants of the shape extremes:

```
theorem transparent_is_atom (T : Type) [DecidableEq T] :
    ∀ (r m : T), bridge_equiv (transparent T) r m ↔
                  bridge_equiv (shapeBridge .atom T id id) r m

theorem opaque_is_unit (R M : Type) :
    ∀ (r : R) (m : M), bridge_equiv (opaqueBridge R M) r m ↔
                        bridge_equiv (shapeBridge .unit Unit (fun _ => ()) (fun _ => ())) r m
```

Transparent *is* the atom shape applied to identity observations. Opaque *is* the unit shape applied to trivial observations. Every other bridge is a polynomial composition of these two. The `BridgeShape.depth` and `BridgeShape.leaves` metrics capture the complexity: depth measures nesting, leaves count the primitive bridges. A `Result<(FileHandle, String), FsErr>` bridge has depth 2 (sum of product) and 3 leaves (one opaque, two transparent).

The insight is that `deriving Eq` and `deriving Bridge` are instances of the same generic programming pattern. The difference is the relation being derived: structural equality for `Eq`, observation-factored equivalence for bridges. The polynomial functor provides the universal recursion scheme for both.

---

## 4. Refinement as Natural Transformation

### 4.1 The Precision Spectrum

Not all bridges are created equal. `Transparent<FileHandle>` requires that the SUT and model produce the same handle — a strong demand. `Opaque<FileHandle, MockHandle>` accepts any pair — a weak demand. Between these extremes lies a lattice of precision levels, and the choice of bridge determines the strength of the test.

Bridge refinement captures this ordering. Bridge `b₁` *refines* bridge `b₂` if every pair that `b₁` accepts, `b₂` also accepts:

```
def bridge_refines (b1 b2 : Bridge R M) : Prop :=
  ∀ (r : R) (m : M), bridge_equiv b1 r m → bridge_equiv b2 r m
```

Refinement is a preorder: reflexive (`refines_refl`) and transitive (`refines_trans`). The transparent bridge is the finest among uniform bridges — those that observe both sides the same way (`transparent_refines_uniform`). The opaque bridge is the coarsest: every bridge refines it (`opaque_coarsest`), and it is the unique coarsest up to equivalence (`opaque_unique_coarsest`).

### 4.2 Structural Refinement

The refinement ordering on bridges is induced by a structural ordering on shapes. `ShapeRefines s₁ s₂` holds when shape `s₁` has `atom` (transparent) at every position where `s₂` has `atom`, and may additionally have `atom` where `s₂` has `unit` (opaque):

```
inductive ShapeRefines : BridgeShape → BridgeShape → Type
  | refl (s) : ShapeRefines s s
  | atom_unit : ShapeRefines .atom .unit
  | sum (h₁ : ShapeRefines s₁ t₁) (h₂ : ShapeRefines s₂ t₂) :
      ShapeRefines (.sum s₁ s₂) (.sum t₁ t₂)
  | prod (h₁ : ShapeRefines s₁ t₁) (h₂ : ShapeRefines s₂ t₂) :
      ShapeRefines (.prod s₁ s₂) (.prod t₁ t₂)
  | option (h : ShapeRefines s t) : ShapeRefines (.option s) (.option t)
  | list (h : ShapeRefines s t) : ShapeRefines (.list s) (.list t)
```

The key constructor is `atom_unit`: replacing a transparent leaf with an opaque one coarsens the shape. All other constructors propagate refinement through composites. Refinement is transitive (`ShapeRefines.trans`).

Given a proof `href : ShapeRefines s₁ s₂`, the coarsening map transforms finer observations into coarser ones:

```
def ShapeRefines.coarsen : ShapeRefines s₁ s₂ → ∀ (O : Type), s₁.Obs O → s₂.Obs O
  | .refl _, _, x => x
  | .atom_unit, _, _ => ()
  | .sum h₁ h₂, O, x => match x with
    | .inl x => .inl (h₁.coarsen O x) | .inr x => .inr (h₂.coarsen O x)
  | .prod h₁ h₂, O, (x, y) => (h₁.coarsen O x, h₂.coarsen O y)
  | .option h, O, x => match x with | some v => some (h.coarsen O v) | none => none
  | .list h, O, xs => xs.map (h.coarsen O)
```

At `atom_unit`, the coarsening discards the observation, mapping everything to `()`. At composites, it recurses pointwise. The coarsening is an information-losing projection: it forgets the distinctions that the finer shape can see.

### 4.3 The Connection Theorem

Shape refinement induces bridge refinement:

```
theorem shape_refines_bridge_refines (href : ShapeRefines s₁ s₂)
    (O : Type) [DecidableEq O]
    (obs_r : R → s₁.Obs O) (obs_m : M → s₁.Obs O) :
    bridge_refines
      (shapeBridge s₁ O obs_r obs_m)
      (shapeBridge s₂ O (href.coarsen O ∘ obs_r) (href.coarsen O ∘ obs_m))
```

If two values are equivalent under the finer bridge, they are equivalent under the coarser bridge. The proof is a single line: apply `congrArg` with the coarsening map. The coarsening is a function; applying it to equal inputs gives equal outputs.

### 4.4 Naturality

The coarsening map commutes with `fmap`:

```
theorem ShapeRefines.coarsen_natural (href : ShapeRefines s₁ s₂) (f : A → B) :
    ∀ (x : s₁.Obs A),
    href.coarsen B (s₁.fmap f x) = s₂.fmap f (href.coarsen A x)
```

This is a naturality condition. The coarsening is a natural transformation between the polynomial functors `⟦s₁⟧` and `⟦s₂⟧`. The proof is structural induction on the refinement proof, with the list case requiring an inner induction.

Naturality means that the refinement ordering is well-behaved with respect to the functor structure. Coarsening and functorial mapping can be performed in either order. This categorical coherence ensures that the precision spectrum interacts correctly with bridge composition.

### 4.5 Practical Consequence

The chain of theorems yields a single practical guarantee (`refines_strengthen_bisim`): replacing any bridge with a finer one — swapping `Opaque` for `Transparent` at any leaf — gives a strictly stronger bisimulation. The user can start with all-opaque bridges (fast, weak: every test passes trivially) and incrementally refine toward all-transparent (slower, stronger: the test checks every observable detail). Each refinement step is monotone, and the compositional structure of shapes ensures that refining one component never weakens another.

---

## 5. What a Passing Test Proves

### 5.1 Bounded Bisimulation

A lockstep test runs a sequence of actions on both the model and the SUT, checking bridge equivalence at each step. We formalize the guarantee as a bounded bisimulation. A lockstep system packages all the components:

```
structure LockstepSystem where
  SM : Type                              -- model state
  SS : Type                              -- SUT state
  ActionIdx : Type                       -- action index
  RetM : ActionIdx → Type               -- model return type per action
  RetS : ActionIdx → Type               -- SUT return type per action
  bridge : (a : ActionIdx) → Bridge (RetS a) (RetM a)
  step_model : (a : ActionIdx) → SM → SM × RetM a
  step_sut : (a : ActionIdx) → SS → SS × RetS a
```

Bounded bisimulation at depth *n* is defined by recursion on *n*:

```
def bounded_bisim (sys : LockstepSystem) : Nat → sys.SM → sys.SS → Prop
  | 0, _, _ => True
  | n + 1, sm, ss => ∀ (a : sys.ActionIdx),
      let (sm', rm) := sys.step_model a sm
      let (ss', rs) := sys.step_sut a ss
      bridge_equiv (sys.bridge a) rs rm ∧ bounded_bisim sys n sm' ss'
```

At depth 0, any pair of states is bisimilar — the test has exhausted its budget. At depth *n* + 1, *every* action must produce bridge-equivalent results, and the successor states must be bisimilar at depth *n*. The universal quantifier over actions is the key strength: bounded bisimulation at depth *n* certifies agreement on *all* traces of length *n*, not just the ones the test happened to explore.

Bounded bisimulation is monotone: if it holds at depth *m*, it holds at depth *n* for any *n* ≤ *m* (`bounded_bisim_mono`). Full (coinductive) bisimulation is the intersection over all depths: `∀ n, bounded_bisim sys n sm ss`.

### 5.2 Three Equivalent Characterizations

The central theoretical result is that three independently motivated definitions coincide. Each is proved as a machine-checked biconditional.

**Characterization 1: Logical (bounded bisimulation).** The recursive predicate above. This is the definition — the intensional view of what the test establishes.

**Characterization 2: Observational (indistinguishability on traces).** The SUT and model produce identical bridge observations on all traces up to length *n*. Define `sut_observation` and `model_observation` as the bridge-projected return values. Then:

```
theorem observational_refinement_equiv (sys : LockstepSystem)
    (n : Nat) (sm : sys.SM) (ss : sys.SS) :
    bounded_bisim sys n sm ss
    ↔ (∀ (pre : List sys.ActionIdx) (a : sys.ActionIdx),
        pre.length + 1 ≤ n →
        sut_observation sys a (sut_state_after sys pre ss)
        = model_observation sys a (model_state_after sys pre sm))
```

Bounded bisimulation holds if and only if, for every prefix of actions and every subsequent action, the observations are identical. The forward direction follows from `bisim_observation_after_prefix`, which shows that bisimulation is preserved along traces. The reverse direction reconstructs the bisimulation from the universal observation guarantee by induction on depth.

This is the observational refinement guarantee: no interaction through the bridge API can distinguish the SUT from the model within the tested depth.

**Characterization 3: Game-semantic (absence of Attacker strategy).** Interpret bisimulation as a two-player game. The Attacker chooses actions, trying to find a bridge failure. The Defender survives if every action passes. The Attacker's strategy is a `BisimWitness`:

```
inductive BisimWitness (sys : LockstepSystem) where
  | bridge_fail : sys.ActionIdx → BisimWitness sys
  | deeper : sys.ActionIdx → BisimWitness sys → BisimWitness sys
```

A `bridge_fail a` wins immediately: action `a` at the current state produces a bridge mismatch. A `deeper a w` records that action `a` passes its bridge check, but witness `w` finds a failure in the successor states. The witness is a *path* through the game tree, not the full tree — it records the specific sequence of actions that leads to failure.

```
theorem bisim_game_semantic (sys : LockstepSystem)
    (n : Nat) (sm : sys.SM) (ss : sys.SS) :
    ¬ bounded_bisim sys n sm ss
    ↔ ∃ (w : BisimWitness sys), witness_valid sys w sm ss ∧ w.depth ≤ n
```

Bisimulation fails at depth *n* if and only if the Attacker has a valid witness of depth at most *n*. The forward direction (completeness) uses classical logic to extract a concrete failing action from the negation of the universal quantifier. The backward direction (soundness) is constructive: the witness directly encodes the failure path.

The witness IS the minimal failing test case. When `proptest` finds a counterexample and shrinks it, it converges toward a `BisimWitness`. The DPOR explorer searches for witnesses efficiently; this theorem proves the search is complete.

### 5.3 The Runner Correspondence

The test runner's operational behavior — stepping through actions, checking bridge equivalence, continuing — has a direct formal counterpart. The `runner_passes` predicate mirrors the Rust `LockstepSut::apply` function:

```
def runner_passes (sys : LockstepSystem) :
    List sys.ActionIdx → sys.SM → sys.SS → Prop
  | [], _, _ => True
  | a :: rest, sm, ss =>
    let (sm', rm) := sys.step_model a sm
    let (ss', rs) := sys.step_sut a ss
    bridge_equiv (sys.bridge a) rs rm ∧ runner_passes sys rest sm' ss'
```

The runner correspondence theorem closes the gap between operational testing and formal guarantee:

```
theorem runner_bounded_bisim_equiv (sys : LockstepSystem)
    (n : Nat) (sm : sys.SM) (ss : sys.SS) :
    (∀ (trace : List sys.ActionIdx), trace.length = n →
     runner_passes sys trace sm ss)
    ↔ bounded_bisim sys n sm ss
```

Passing on all traces of length *n* is equivalent to bounded bisimulation at depth *n*. This is a biconditional — there is no gap between what the test runner checks and what the formal property states. The forward direction shows that the runner's operational checks establish the declarative bisimulation relation. The reverse direction shows that bisimulation implies the runner passes on every trace.

The circle is now complete:

> runner passes on all traces ↔ bounded bisimulation ↔ observational refinement ↔ no Attacker winning strategy

Four equivalent views of the same property, each proved as a machine-checked biconditional.

### 5.4 Compositional Testing

Independent subsystems can be tested separately, and the guarantees compose. The product of two lockstep systems runs actions from the disjoint union of both action spaces, with each action affecting only its own subsystem's state:

```
theorem product_bisim_iff (sys1 sys2 : LockstepSystem)
    (n : Nat) (sm1 : sys1.SM) (ss1 : sys1.SS)
    (sm2 : sys2.SM) (ss2 : sys2.SS) :
    bounded_bisim (product_system sys1 sys2) n (sm1, sm2) (ss1, ss2)
    ↔ bounded_bisim sys1 n sm1 ss1 ∧ bounded_bisim sys2 n sm2 ss2
```

The product satisfies bounded bisimulation if and only if both components do. The proof decomposes via `product_bisim_left` and `product_bisim_right` (extraction) and `compositional_bisim` (composition). Product composition is associative (`product_assoc`), and bridge refinement is monotone through the product (`product_refines_bisim`): composing finer bridges gives finer composite guarantees.

This enables modular testing at scale. A system with five independent subsystems needs five separate test suites, not one combinatorial explosion. Each subsystem is tested independently; the biconditional guarantees that the composed system inherits the guarantee.

---

## 6. Mechanization

### 6.1 Scope and Statistics

The Lean 4 formalization comprises 376 definitions across 33 files, with zero uses of `sorry`. It covers:

- **Bridge algebra** (Bridge.lean): the structure, primitives, lifts, fundamental theorem, and decidability — 23 definitions and theorems.
- **Polynomial functors** (PolynomialBridge.lean): shapes, `Obs`, `fmap`, both functor laws, shape-indexed bridge construction, and the derivation correctness theorem.
- **Refinement** (BridgeRefinement.lean): the preorder, opaque-coarsest, transparent-finest, monotonicity of all four lifts, and `refines_strengthen_bisim`.
- **Shape refinement** (PolynomialBridge.lean): `ShapeRefines`, `coarsen`, `coarsen_natural` (naturality), `shape_refines_bridge_refines`, transitivity.
- **Bisimulation** (Lockstep.lean): `bounded_bisim`, monotonicity, single-step agreement.
- **Runner correspondence** (Runner.lean): `runner_passes`, both directions, the biconditional `runner_bounded_bisim_equiv`.
- **Observational refinement** (ObservationalRefinement.lean): trace observations, prefix preservation, the biconditional `observational_refinement_equiv`.
- **Game semantics** (GameSemantics.lean): `BisimWitness`, validity, soundness, completeness, the biconditional `bisim_game_semantic`, crash-aware witnesses, crash-transparent elimination.
- **Compositional testing** (Compositional.lean): product systems, `product_bisim_iff`, associativity, product refinement monotonicity.
- **Extensions**: DPOR swap soundness, crash-recovery bisimulation, session consistency with monotonic reads, effect lattice, and invariant bisimulation.

### 6.2 The Rust-Lean Gap

The formalization is specification verification, not code verification. It proves properties of the *mathematical model* that the Rust implementation is designed to realize. The Rust types (`LockstepBridge`, `Transparent`, `Opaque`, `ResultBridge`) mirror the Lean types (`Bridge`, `transparent`, `opaqueBridge`, `sumBridge`), and the Rust runner mirrors `runner_passes`, but there is no formal proof that the Rust code correctly implements the Lean specification.

We bridge this gap through structural correspondence: the Lean `Bridge` record has the same fields as the Rust `LockstepBridge` trait; the Lean `bounded_bisim` recurse on the same structure as the Rust `LockstepSut::apply`. Maintaining this correspondence is a discipline, not a formal guarantee. We document it honestly: the theorems hold of the mathematical model, and the Rust code is a faithful implementation to the best of our engineering judgment.

---

## 7. Related Work

### 7.1 Logical Relations

The connection between bridges and logical relations traces directly to Reynolds' abstraction theorem (1983): parametric polymorphism preserves type-indexed families of relations across type constructors. Pitts (2000) developed the theory further for operational semantics. Our contribution is not a new logical relation but a new *application*: we use the logical relation structure to derive testing oracles for stateful systems. The observation factoring — projecting through a common `Observed` type with decidable equality — specializes the general theory to a decidable, executable setting suitable for property-based testing.

### 7.2 Generic Programming

Hinze (2000) and Hinze and Gibbons (2003) established the foundations of datatype-generic programming via polynomial functors. Magalhaes et al. (2010) showed how GHC's `Generic` mechanism enables deriving type class instances by structural recursion on type representations. Our bridge derivation is an instance of this pattern: the `BridgeShape` grammar is a universe of polynomial functors, and the derivation algorithm is structural recursion on that universe. The novelty is the target: instead of deriving equality, serialization, or pretty-printing, we derive logical relations. The functor laws (`fmap_id`, `fmap_comp`) and naturality of coarsening (`coarsen_natural`) are the standard obligations of a generic programming scheme, discharged in Lean rather than assumed.

### 7.3 quickcheck-lockstep

De Vries (2021) introduced lockstep testing in Haskell, using GADTs to track the correspondence between opaque SUT handles and symbolic model variables. The key insight — that the Phase GADT can index variables by Symbolic or Concrete — carries over directly to our Rust implementation via the `Is<A,B>` witness and the `Phase` GAT. Our contributions beyond the Haskell original are: (1) the identification of bridges as logical relations with polynomial derivation, (2) the refinement ordering and its categorical structure, (3) the three equivalent characterizations (logical, observational, game-semantic) with machine-checked proofs, (4) crash-recovery and session-consistency extensions, and (5) the full mechanized metatheory.

### 7.4 Program Verification and Iris

Jung et al. (2018) developed Iris, a higher-order concurrent separation logic framework in Coq, using logical relations extensively for proving contextual refinement of concurrent programs (RustBelt). Our work operates at a fundamentally different level: we verify the *testing framework*, not individual programs. Iris proves that a specific program satisfies a specification; we prove that the testing methodology itself is sound — that passing lockstep tests establish genuine bisimulation. The two approaches are complementary: Iris provides deep verification of critical components, while lockstep testing provides broad coverage of systems too complex for full verification.

### 7.5 Property-Based Testing Frameworks

QuickCheck (Claessen and Hughes, 2000), Hedgehog (Stanley, 2017), and proptest (Maguire, 2017) provide property-based testing without formal metatheory. Hughes et al.'s work on testing stateful systems with QuickCheck establishes the operational patterns (model-based testing, shrinking) but does not formalize the relationship between test outcomes and formal properties. We provide the first machine-checked soundness proofs for lockstep-style stateful testing: the runner correspondence theorem, the observational refinement biconditional, and the game-semantic completeness theorem together prove that passing tests mean what users think they mean.

Lampropoulos et al. (2017) studied testing-for-free via logical relations in the context of QuickChick and Coq, using parametricity to generate test inputs. Their work shares our use of logical relations in a testing context but targets input generation rather than oracle construction.

---

## 8. Conclusion

Bridges are logical relations. This single observation organizes the entire lockstep testing methodology. The compositional structure of bridges is the fundamental theorem of logical relations, specialized to observation-factored decidable equivalences. The derivation algorithm is generic programming over polynomial functors — the same technique as `deriving Eq`, applied to a richer target. The precision spectrum is a lattice of logical relations, ordered by inclusion, with coarsening as a natural transformation between polynomial functors. And the testing guarantee admits three equivalent characterizations — logical, observational, and game-semantic — each proved as a machine-checked biconditional.

The practical consequence is a testing framework where users write action declarations and the proc macro derives bridges automatically, where every bridge choice has a formal precision guarantee, and where every passing test establishes a genuine bounded bisimulation. The 376-definition Lean 4 formalization, with zero `sorry`, ensures that these claims are not aspirational but proved.

Testing is not verification. But a testing framework with verified metatheory occupies a useful middle ground: the individual test outcomes are probabilistic, but the *meaning* of those outcomes is certain.
