# Research Ideation — Round 2: Five Ideas Enabled by the Formalization

The 119-theorem Lean formalization changes what's possible. The previous ideation (Round 1) generated ideas based on the *library*. This round generates ideas based on the *metatheory* — things that only make sense because we have machine-checked proofs of soundness, completeness, and observational refinement.

## Idea 1: Certified Bridge Synthesis via Proof Search

**One-sentence pitch:** Use the Lean formalization as a *synthesizer*: given a pair of Rust types and an opaque map, have Lean produce a bridge AND a correctness proof, then extract the bridge back to Rust — certified compilation of test oracles.

### The Problem

The proc macro's `derive_bridge` operates on syntax (string-matched type names). It gets basic cases right but has no semantic understanding: it can't handle type aliases, module-qualified paths, or user-defined type constructors. More fundamentally, its correctness is informal — we trust the macro code, not a proof.

### The Key Insight

The Lean formalization already has the bridge algebra, all the lift theorems, and the `BridgeSpec` inductive. Instead of deriving bridges in Rust and proving them sound in Lean separately, **derive them in Lean directly** using tactic-based proof search, then extract the synthesized bridge to Rust code via a Lean metaprogram.

```lean
-- The user specifies the type structure declaratively:
def mySpec : BridgeSpec := .sum (.prod .opaque .transparent) .transparent

-- Lean synthesizes the bridge and its proof:
#eval synthesize_bridge mySpec
-- Output: "ResultBridge<TupleBridge<Opaque<R, M>, Transparent<A>>, Transparent<E>>"
-- Plus: a proof term for bridge_equiv preservation
```

The Lean metaprogramming environment can enumerate valid bridges and prove each one correct. The output is a Rust type expression AND a certificate. The Rust proc macro calls out to Lean during compilation (or reads pre-computed certificates).

### What Makes This Novel

The combination of:
1. Proof-carrying bridge synthesis (not just derivation)
2. Lean-as-synthesizer for Rust code generation
3. Certified cross-language compilation of test oracles
4. The 119-theorem formalization is the *trusted computing base*, not the proc macro

Nobody has used a proof assistant as a synthesizer for property-based testing infrastructure. The closest work is Liquid Haskell generating tests from refinement types, but that's test *generation*, not oracle *synthesis*.

### Concrete Architecture

```
User writes: opaque_types = { FileHandle => MockHandle }
  ↓
Proc macro extracts type structure → BridgeSpec
  ↓
Lean proof search finds bridge matching BridgeSpec
  ↓
Lean outputs: (bridge_type : String, proof : Certificate)
  ↓
Proc macro emits bridge_type into Rust code
Certificate stored for audit
```

### Assessment

- **Novelty**: Very High — proof-carrying synthesis of test oracles is new
- **Difficulty**: High (3-4 months) — Lean metaprogramming + cross-language bridge
- **Impact**: Very High — certifies the entire bridge derivation pipeline
- **Crux**: The Lean-to-Rust type serialization; handling the impedance mismatch between Lean's type universe and Rust's
- **Publishability**: POPL — certified compilation of testing infrastructure


## Idea 2: Differential Bridge Testing

**One-sentence pitch:** Given two bridges for the same type pair (one coarser, one finer), use the refinement ordering to automatically test whether the coarser bridge misses real bugs — a meta-testing technique enabled by `refines_strengthen_bisim`.

### The Problem

Users choose bridges manually (or let the proc macro derive them). A common mistake is using `Opaque` where `Transparent` would be appropriate — making the test weaker than necessary. Currently, there's no way to detect this.

### The Key Insight

The `refines_strengthen_bisim` theorem says: if you upgrade a bridge to a finer one, any test that passed before still passes. The *contrapositive*: if a test *fails* with the finer bridge but *passes* with the coarser bridge, the coarser bridge is *hiding a bug*.

This gives us a fully automatic way to detect overly-coarse bridges:

```rust
// User's original bridge (coarser):
bridge = "ResultBridge<Opaque<Handle, MockHandle>, Transparent<Err>>"

// Auto-generated finer bridge (for differential testing):
bridge_fine = "ResultBridge<Transparent<Handle>, Transparent<Err>>"  // if Handle == MockHandle
```

Run both bridges on the same traces. If the fine bridge catches failures the coarse one misses, report: "Your `Opaque` bridge on `Handle` is masking failures. Consider using `Transparent` if `Handle` and `MockHandle` are the same type."

### Concrete Sketch

```rust
/// Automatically generate the finest possible bridge for a type pair.
fn finest_bridge(real: &syn::Type, model: &syn::Type) -> TokenStream2 {
    // All leaves that COULD be Transparent (same type on both sides) → Transparent
    // Only leaves that MUST be Opaque (different types) → Opaque
}

/// Run differential bridge testing.
fn differential_bridge_test<M: LockstepModel>(traces: &[Trace]) {
    for trace in traces {
        let coarse_result = run_with_bridge::<CoarseBridge>(trace);
        let fine_result = run_with_bridge::<FineBridge>(trace);
        if coarse_result.is_ok() && fine_result.is_err() {
            report_bridge_weakness(trace, fine_result.err());
        }
    }
}
```

### What Makes This Novel

Using the *bridge refinement preorder* as a testing tool. The formalization guarantees that refinement is monotone, so differential testing is sound: any failure caught by the finer bridge but not the coarser one is a genuine missed bug. No other testing framework has this capability because no other framework has a formal refinement ordering on test oracles.

### Assessment

- **Novelty**: High — meta-testing of test oracles via formal refinement
- **Difficulty**: Medium (4-6 weeks)
- **Impact**: High — directly improves test quality
- **Crux**: Automatically computing the finest bridge (requires type equality analysis)
- **Publishability**: ICFP experience report or ISSTA


## Idea 3: Bisimulation-Guided Shrinking

**One-sentence pitch:** Use the `bug_localization` theorem to guide shrinking: instead of random shrinking, localize which action first violates the bisimulation and shrink the trace to the minimal prefix that triggers it.

### The Problem

proptest's shrinking is generic — it shrinks randomly, guided by the strategy's `ValueTree`. This works but produces non-minimal counterexamples. A failing trace of 20 actions might shrink to 12 actions when the actual bug is exposed by 3 actions at the right depth.

### The Key Insight

`bug_localization` proves: if `bounded_bisim (n+1)` fails, there exists a specific action `a` that witnesses the failure (either the bridge check fails, or the successor bisim fails). This gives a *constructive* shrinking strategy:

1. Run the test and find the failing depth
2. At that depth, find the witnessing action (`bug_localization`)
3. Check if earlier actions can be removed without affecting the failure
4. The bisimulation structure guarantees that the failure depth is monotone — so binary search on the prefix length is sound

### Concrete Sketch

```rust
fn bisim_guided_shrink<M: LockstepModel>(
    failing_trace: &[Box<dyn AnyAction>],
    model: &M::ModelState,
    sut: &M::Sut,
) -> Vec<Box<dyn AnyAction>> {
    // 1. Find the first depth k where bridge_equiv fails
    let k = find_failure_depth(failing_trace, model, sut);

    // 2. The failure is witnessed by the action at position k
    // 3. Try removing actions before position k:
    //    - For each action i < k, check if removing it still causes failure at k-1
    //    - If yes, the action is irrelevant to the bug
    //    - If no, the action is necessary (it sets up state for the failure)

    // 4. Return the minimal sub-trace
    minimize_prefix(failing_trace, k, model, sut)
}
```

The `testing_completeness` theorem guarantees: if the bug exists at depth k, it will be found at depth k. So removing irrelevant actions and re-checking at the (now shorter) depth is sound.

### What Makes This Novel

Using the metatheory's *structure* (bisimulation depth, bug localization) to guide shrinking. This is not random shrinking — it's *semantically guided* shrinking that exploits the lockstep invariant. No other property-based testing framework has formal shrinking guidance because none have a metatheory that exposes failure depth and witnessing actions.

### Assessment

- **Novelty**: High — formally-guided shrinking is new
- **Difficulty**: Medium (3-4 weeks)
- **Impact**: High — better counterexamples are the #1 user request for PBT
- **Crux**: Handling actions that affect preconditions of later actions (dependency analysis)
- **Publishability**: ICFP or Haskell Symposium experience report


## Idea 4: Observational Refinement Contracts

**One-sentence pitch:** Use the `observational_refinement_equiv` biconditional as a *runtime contract system*: the bridge algebra becomes a refinement contract that's checked at the boundary between modules, giving gradual verification for concurrent systems.

### The Problem

The formal guarantee (observational refinement up to depth n) currently lives in the test suite. Once the test passes, the guarantee is inferred — but it's not enforced at runtime. If the SUT's behavior changes after the test was written (e.g., a regression), the refinement contract is silently violated until the test is re-run.

### The Key Insight

The bridge algebra is already a *specification of observable behavior*. Turn it into a runtime contract:

```rust
#[refinement_contract(
    model = "MyModel",
    bridge = "ResultBridge<Transparent<Output>, Transparent<Error>>",
    depth = 10,
)]
pub fn my_api_endpoint(input: Input) -> Result<Output, Error> {
    // actual implementation
}
```

The contract:
1. Runs the model in parallel (on a shadow copy)
2. Checks `bridge_equiv` on every return value
3. Reports violations as contract failures (not panics)
4. The `depth` parameter controls how many chained calls are tracked

### What Makes This Novel

The key innovation is that the contract is *not just "check equality"* — it's bridge-parameterized. Opaque bridges allow the contract to pass on values that differ structurally (handles, IDs) while catching semantic mismatches. This is a form of *gradual refinement verification*:

- `Transparent` everywhere = full trace equivalence checking (strictest)
- `Opaque` everywhere = crash-absence only (weakest)
- Mixed = targeted checking at the right granularity

The `observational_refinement_equiv` theorem guarantees that the contract is *exactly right* — it catches all bugs detectable by the bridge and nothing more.

### Concrete Sketch

```rust
struct RefinementGuard<M: LockstepModel> {
    model: M::ModelState,
    env: TypedEnv,
    depth_remaining: usize,
    violations: Vec<ContractViolation>,
}

impl<M: LockstepModel> RefinementGuard<M> {
    fn check(&mut self, action: &dyn AnyAction, sut_result: &dyn Any) {
        let model_result = M::step_model(&mut self.model, action, &self.env);
        if let Err(msg) = action.check_bridge(&*model_result, sut_result) {
            self.violations.push(ContractViolation { action, msg, depth: self.depth_remaining });
        }
        self.depth_remaining -= 1;
    }
}
```

### Assessment

- **Novelty**: Very High — bridge-parameterized runtime contracts are new
- **Difficulty**: Medium-High (2 months)
- **Impact**: Very High — bridges testing and runtime verification
- **Crux**: Performance overhead of running the model in production (shadow execution)
- **Publishability**: OOPSLA — runtime verification meets property-based testing


## Idea 5: Compositional Bisimulation for Modular Testing

**One-sentence pitch:** Prove that if two subsystems independently satisfy bounded bisimulation, their composition also satisfies bounded bisimulation — enabling modular testing where subsystems are verified independently and composed with machine-checked guarantees.

### The Problem

The current formalization treats the system as monolithic: one `LockstepSystem` with one action space, one model state, one SUT state. Real systems are composed of modules (a database layer + a network layer + a business logic layer). Currently, you must test the entire composed system as one lockstep test, even if each layer was tested independently.

### The Key Insight

Two `LockstepSystem`s can be composed if they share a common interface. The composition theorem would say:

```lean
def compose (sys1 : LockstepSystem) (sys2 : LockstepSystem)
    (glue : sys1.SM × sys2.SM → SM_composed)
    (unglue : SM_composed → sys1.SM × sys2.SM) :
    LockstepSystem

theorem compose_bisim (sys1 sys2 : LockstepSystem)
    (n : Nat)
    (h1 : bounded_bisim sys1 n sm1 ss1)
    (h2 : bounded_bisim sys2 n sm2 ss2)
    (hcompat : actions_compatible sys1 sys2) :
    bounded_bisim (compose sys1 sys2) n (sm1, sm2) (ss1, ss2)
```

The `actions_compatible` condition says: actions from sys1 don't affect the state of sys2, and vice versa. When this holds, the composition bisimulation follows from the component bisimulations.

### What Makes This Novel

Compositional bisimulation for property-based testing. This is well-studied for process algebras (CCS, CSP) but has never been applied to lockstep testing. The bridge algebra makes it work: if sys1 uses `Opaque` for a handle that sys2 depends on, the compositional theorem tells you exactly when this is safe and when it's not.

### Concrete Extensions

1. **Sequential composition**: sys1 runs first, sys2 runs second. The composed action space is the disjoint union, and the state is threaded sequentially. This is the simplest case and directly useful for layered architectures.

2. **Parallel composition**: sys1 and sys2 run concurrently with shared state. This connects to the DPOR formalization: if the actions of sys1 commute with the actions of sys2, the parallel composition preserves bisimulation.

3. **Interface composition**: sys1 produces values that sys2 consumes. The bridge at the interface determines how much information flows between them. An `Opaque` bridge at the interface means sys2 can use sys1's handles without knowing their internal structure — exactly the abstraction boundary pattern.

### Assessment

- **Novelty**: High — compositional bisimulation for PBT is new
- **Difficulty**: High (3-4 months for the theory, another 2 for implementation)
- **Impact**: Very High — enables modular testing of large systems
- **Crux**: The `actions_compatible` condition — defining precisely when composition is sound
- **Publishability**: POPL — compositional reasoning for testing


## Priority Ranking

| Idea | Novelty | Feasibility | Impact | Enabled By |
|------|---------|-------------|--------|------------|
| 1. Certified Bridge Synthesis | Very High | Medium | Very High | BridgeSpec + 119 theorems |
| 2. Differential Bridge Testing | High | High | High | bridge_refines + refines_strengthen_bisim |
| 3. Bisimulation-Guided Shrinking | High | High | High | bug_localization + testing_completeness |
| 4. Observational Refinement Contracts | Very High | Medium | Very High | observational_refinement_equiv |
| 5. Compositional Bisimulation | High | Low-Medium | Very High | bounded_bisim + DPOR |

**Recommendation**: Ideas 2 (Differential Bridge Testing) and 3 (Bisimulation-Guided Shrinking) are the best next steps — both are highly feasible, directly improve the user experience, and are *uniquely enabled* by the formalization. No other testing framework can do either of these because none have the formal bridge refinement ordering or the bug localization theorem.

For the ambitious follow-up: Idea 5 (Compositional Bisimulation) is the POPL paper. Idea 4 (Runtime Contracts) is the OOPSLA paper. Idea 1 (Certified Synthesis) is the "wow factor" paper but requires the most infrastructure.
