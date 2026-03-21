# Research Ideation: Five Deep Ideas for proptest-lockstep

## Idea 1: Effect-Indexed Commutativity Lattice

**One-sentence pitch:** Annotate each action with an effect signature from a static lattice, and derive commutativity for free -- replacing the O(n^2) dynamic model oracle with an O(1) lattice lookup.

### The Problem

The DPOR implementation is elegant but expensive: `operations_commute` clones the model state twice, runs both orderings, and compares via `PartialEq`. For a linearizability check with k operations per branch and b branches, this is O(k^2 b^2) model executions per interleaving.

### The Key Insight

Most actions interact with the SUT through a small set of resources (keys in a KV store, file handles, channels). Two actions commute iff their resource footprints don't conflict. This is exactly the structure of a conflict algebra: a pre-order on effects where commutativity is decidable from the effect annotations alone.

```rust
trait ResourceFootprint {
    type Effect: ConflictAlgebra;
    fn effect(&self) -> Self::Effect;
}

trait ConflictAlgebra: PartialOrd + Clone {
    fn commutes_with(&self, other: &Self) -> bool;
}
```

For a KV store:

```rust
enum KvEffect {
    Read(Key),
    Write(Key),
    ReadAll,
    WriteAll,
}
```

Where `Read(k1)` commutes with `Read(k2)` (always), `Read(k1)` commutes with `Write(k2)` iff `k1 != k2`, etc.

### Concrete Sketch

Extend the proc macro:

```rust
#[action(
    real_return = "Option<String>",
    bridge = "OptionBridge<Transparent<String>>",
    effect = "KvEffect::Read(self.key.clone())",
)]
pub struct Get { pub key: String }
```

The model oracle becomes a fallback for actions without effect annotations -- graceful degradation, not a breaking change.

### What Makes This Novel

The combination of:
1. Static effect lattice for fast pruning (from database/concurrency theory)
2. Dynamic model oracle as fallback for unannotated actions
3. Proc-macro-derived effects from action structure
4. Formal connection: the effect lattice is a sound approximation of the model oracle (provable in Lean)

### Assessment

- **Novelty**: High
- **Difficulty**: ~2 months engineering, 1 month formalization
- **Impact**: High
- **Crux**: Getting the lattice right for compound effects (read-set, write-set products)
- **Publishability**: ICFP experience report


## Idea 2: Bridge Functors and Polynomial Derivation

**One-sentence pitch:** Bridges are natural transformations between observation functors, and every algebraic data type's bridge can be derived mechanically from its polynomial functor decomposition.

### The Problem

Users currently write bridges by hand:

```rust
bridge = "ResultBridge<TupleBridge<Opaque<FileHandle, MockHandle>, Transparent<String>>, Transparent<FsErr>>"
```

This is correct but verbose. The bridge exactly mirrors the structure of the return type -- this structural mirroring is a sign that the bridge is derivable.

### The Key Insight

Every Rust type built from `()`, products, sums, `Option`, and `Vec` has a polynomial functor decomposition. A bridge between `F(R1, ..., Rn)` and `F(M1, ..., Mn)` is determined by bridges between each `Ri` and `Mi` -- it's functorial.

### Concrete Sketch

A derive macro that reads the return type structure and emits the bridge:

```rust
#[action(
    real_return = "Result<(FileHandle, String), FsErr>",
    model_return = "Result<(MockHandle, String), FsErr>",
    opaque_types = { FileHandle => MockHandle },
)]
pub struct Open { pub path: String }
```

The derivation algorithm:
1. Parse `real_return` and `model_return` into type ASTs
2. Walk both trees in lockstep
3. At each node:
   - Types identical -> `Transparent<T>`
   - Types differ and in `opaque_types` -> `Opaque<R, M>`
   - Types differ and NOT in `opaque_types` -> error
   - `Result<A, B>` -> `ResultBridge<bridge(A_r, A_m), bridge(B_r, B_m)>`
   - `(A, B)` -> `TupleBridge<bridge(A_r, A_m), bridge(B_r, B_m)>`
   - `Option<A>` -> `OptionBridge<bridge(A_r, A_m)>`
   - `Vec<A>` -> `VecBridge<bridge(A_r, A_m)>`

### What Makes This Novel

The polynomial functor derivation of bridges is new. The theoretical basis: logical relations for polynomial functors are themselves polynomial, so the bridge derivation is structurally recursive. The Lean formalization extends naturally: prove that for any polynomial functor F, the derived bridge preserves `bridge_equiv`.

The research contribution: bridges are the generic programming of logical relations. Just as `deriving Eq` gives structural equality, `deriving Bridge` gives structural observation.

### Assessment

- **Novelty**: High
- **Difficulty**: ~3 weeks for the derive macro, ~1 month for the Lean generics
- **Impact**: High
- **Crux**: Handling recursive types (Vec<T> is mu X. 1 + T x X)
- **Publishability**: ICFP functional pearl


## Idea 3: Model-Coverage-Guided Generation (MCGG)

**One-sentence pitch:** Use the model's reachable state space as a coverage map to guide action generation toward unexplored states, turning property-based testing into a directed model exploration.

### The Problem

Current action generation is essentially random-with-preconditions. Random generation hits "common" states repeatedly and rarely explores boundary cases.

### The Key Insight

The model is pure, cheap to clone, and contains the meaning of the system state. Instead of code-line coverage (syntactic), use model state coverage (semantic):

```rust
trait CoverageGuided: LockstepModel {
    fn coverage_key(state: &Self::ModelState) -> u64;
}
```

### Concrete Sketch

```rust
fn gen_action_coverage_guided<M: CoverageGuided>(
    state: &M::ModelState,
    env: &TypedEnv,
    coverage: &mut HashSet<u64>,
) -> BoxedStrategy<Box<dyn AnyAction>> {
    // Generate N candidate actions
    // For each, run the model forward (cheap: pure clone)
    // Score by: did the successor state's coverage_key land in a new bucket?
    // Bias generation toward actions that explore new buckets
}
```

### What Makes This Novel

The combination of:
1. Semantic coverage (model state, not code lines) -- nobody does this
2. Forward simulation for candidate scoring -- the model is cheap
3. Integration with lockstep -- the model exists already, so the coverage oracle is free
4. Connection to DPOR -- coverage-guided generation produces more diverse traces

Closest existing work:
- AFL/libFuzzer: code coverage, not semantic
- Swarm testing (Groce et al.): random parameter variation, not state-directed
- Targeted PBT (Loscher & Sagonas, 2017): fitness-guided but for specific properties

Nobody has combined model-based testing with coverage-guided generation where the model IS the coverage oracle.

### Assessment

- **Novelty**: Very High
- **Difficulty**: ~2 weeks prototype, ~2 months to get generation weighting right
- **Impact**: Very High
- **Crux**: The coverage function granularity (abstract interpretation)
- **Publishability**: ICFP/ISSTA crossover


## Idea 4: Observational Refinement as a Free Theorem

**One-sentence pitch:** The bridge algebra gives a Reynolds-style abstraction theorem for free: any program interacting with the SUT only through bridged observations cannot distinguish the SUT from the model.

### The Key Insight

Reynolds' abstraction theorem (1983) says: if a function is parametrically polymorphic, it respects all logical relations.

Our version: if a test interacts with the SUT only through actions whose results are checked via bridges, and all checks pass, then the SUT and model are observationally equivalent at the granularity of the bridge.

### The Formal Statement

```lean
theorem bridge_parametricity (sys : LockstepSystem) (sm : sys.SM) (ss : sys.SS)
    (n : Nat) (h : bounded_bisim sys n sm ss)
    (ctx : Context sys)
    (hctx : ctx.depth <= n) :
    bridge_equiv (ctx.bridge) (ctx.run_sut ss) (ctx.run_model sm)
```

Where `Context` is a sequence of at most `n` actions composed with projections.

### Assessment

- **Novelty**: Very High
- **Difficulty**: 2-3 months of Lean work
- **Impact**: Very High (POPL-level theory)
- **Crux**: Defining `Context` cleanly -- it's a strategy (function from histories to actions)


## Idea 5: Incremental Linearizability via State-Based Memoization

**One-sentence pitch:** Replace brute-force interleaving enumeration with memoization of bridge failures keyed by model state, pruning entire classes of interleavings.

### The Key Insight

When operation A from branch 1 fails the bridge check at position i with model state S, and later you reach the same state S at position i via a different prefix, you can prune A without retrying.

```rust
let mut failure_cache: HashMap<(u64, usize), bool> = HashMap::new();
```

### Why This Is Better Than Pure DPOR

DPOR prunes based on commutativity (eliminates equivalent interleavings). State-based memoization prunes based on bridge failure (eliminates impossible interleavings). These are complementary.

### Assessment

- **Novelty**: Medium
- **Difficulty**: ~3 weeks, requires Hash on model states
- **Impact**: Medium
- **Crux**: Model state hashing (need Hash trait bound, natural for most models)
- **Publishability**: Workshop paper


## Priority Ranking

| Idea | Novelty | Feasibility | Impact | Publishability |
|------|---------|-------------|--------|----------------|
| 1. Effect-Indexed Commutativity | High | Medium | High | ICFP experience report |
| 2. Polynomial Bridge Derivation | High | High | High | ICFP functional pearl |
| 3. Model-Coverage-Guided Generation | Very High | Medium | Very High | ICFP/ISSTA crossover |
| 4. Observational Refinement Free Theorem | Very High | Low | Very High | POPL-level theory |
| 5. Incremental Linearizability | Medium | High | Medium | Workshop paper |

**Recommendation**: Idea 2 (polynomial bridge derivation) is the best next step -- highly feasible, makes the library dramatically more ergonomic, has a clean story for a functional pearl, and extends the Lean formalization naturally. Then Idea 3 (MCGG) for the ambitious follow-up -- it's the most novel and would be a genuine first in the testing literature.
