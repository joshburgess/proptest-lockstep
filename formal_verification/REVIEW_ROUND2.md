# Research Critic Review — Round 2

## Summary

proptest-lockstep is a Rust library for lockstep-style stateful property testing, accompanied by a comprehensive Lean 4 formalization (12 files, 119 theorems/definitions, zero `sorry`) and a proc macro with polynomial bridge derivation. Since the last review, the project has closed every identified gap: the tautological `lockstep_test_sound` is replaced by a substantive runner correspondence biconditional, DPOR soundness is machine-checked, opaque handle detection is formalized, precondition filtering is proved conservative, and a new observational refinement theorem closes the chain `runner passes ↔ bounded_bisim ↔ observational refinement`. Criterion benchmarks for DPOR effectiveness are now included.

## Strengths

- **[S1] The runner correspondence theorem is the right theorem.** `runner_bounded_bisim_equiv` proves that passing on all traces of length n is *equivalent* to bounded bisimulation at depth n — not just an implication in one direction. This is exactly what was missing in the last review [W1]. The proof structure (induction on n, extracting bridge checks from specific traces, applying the IH at successor states) is clean and follows the structure of the Rust runner.

- **[S2] The observational refinement biconditional is genuinely non-trivial.** `observational_refinement_equiv` proves that bounded_bisim is equivalent to per-step observation equality along all traces. The reverse direction (observation equality implies bisim) requires a careful induction where the empty prefix gives the bridge check and prepending an action gives the successor bisim. This is not a trivial restatement — it establishes that `bounded_bisim` is the *exact* characterization of observational indistinguishability.

- **[S3] The DPOR formalization is clean and practically relevant.** `dpor_swap_sound` proves the fundamental lemma directly by rewriting with the three commutativity equalities (state, result-of-a, result-of-b). The extension to `dpor_swap_at` via `linearization_check_append` is elegant. The formalization's use of direct equality on results (stronger than the Rust bridge-based check) is correctly noted as conservative.

- **[S4] Testing completeness closes the theoretical story.** `testing_completeness` plus `testing_sound_and_complete` means the system now has a *complete* metatheory for deterministic lockstep testing: any observable bug is detected, and no passing test gives a false guarantee. For a property-based testing framework, this is a rare level of formal assurance.

- **[S5] The polynomial bridge derivation bridges theory and practice.** The proc macro's `derive_bridge` eliminates the most common source of user error (writing long bridge type expressions), and the `DerivedBridge.lean` formalization proves the derivation preserves bridge_equiv and is monotone in refinement. Having both the engineering artifact and its formal soundness proof is a model for verified tooling.

- **[S6] The formalization is impressively comprehensive for a testing tool.** 119 theorems across 12 files covering sequential testing (bridge algebra, runner, soundness, completeness, observational refinement), concurrent testing (DPOR, linearizability), opaque handles, preconditions, bridge refinement, and derived bridges. No other property-based testing framework has anything close to this level of formal assurance.

- **[S7] The benchmarks add empirical credibility.** The Criterion benchmarks measuring DPOR pruning ratio, commutativity check cost, and scaling behavior provide concrete data. The ~200ns per commutativity check and linear scaling under DPOR for disjoint workloads are useful data points.

## Weaknesses

- **[W1] The `LockstepSystem` in Lean is still idealized relative to the Rust runner.** The Lean model has `step_model : ActionIdx → SM → SM × RetM a` — a pure function with no environment (TypedEnv). The Rust runner passes an environment for GVar resolution and stores results in it after each step. This means the formal model doesn't capture how GVar projection chains work, which is one of the library's key features. The gap is documented honestly, but it means the strongest formal guarantee doesn't cover the most complex usage pattern (opaque handles with GVar projections).

- **[W2] `bug_localization` relies on classical logic unnecessarily.** The proof uses `Classical.byContradiction` to extract the witness, but `bounded_bisim` at depth n+1 unfolds constructively — there should be a direct proof that avoids classical reasoning. Specifically, `bounded_bisim (n+1) sm ss` unfolds to `∀ a, bridge_equiv ... ∧ bounded_bisim n ...`, and its negation should be decomposable without excluded middle. This is a style issue, not a soundness issue, but a constructive proof would be stronger.

- **[W3] The `DerivedBridge.lean` formalization doesn't connect `BridgeSpec` to concrete bridges.** `BridgeSpec` is defined as a standalone inductive type, but there's no interpretation function `BridgeSpec → Bridge R M` (which would require dependent types on the spec to track R and M). The theorems about derived bridge preservation just re-state the existing lift theorems. The `BridgeSpec` is a description of the *shape* of a derived bridge, but the formalization doesn't prove that a bridge *matching* a given spec preserves bridge_equiv — it proves each individual lift does, which was already known.

- **[W4] No empirical evaluation of the polynomial bridge derivation.** The benchmarks cover DPOR/linearizability but not the bridge derivation feature. Measurements of compilation time impact (proc macro overhead), error message quality for malformed types, and user study or LOC reduction metrics would strengthen the tool paper story.

- **[W5] The `model_commute` formalization uses direct equality on results, but the Rust implementation uses `check_bridge`.** This is documented, but the consequence is that the DPOR soundness proof doesn't cover custom bridges where `observe_real ≠ observe_model`. A bridge where the real observation function is lossy (e.g., hashes the result) could cause `check_bridge` to report commutativity when the underlying results differ. The formalization proves DPOR sound for an idealized commutativity check, not the actual one.

- **[W6] Several theorems are thin wrappers.** `full_trace_refinement` is `bounded_bisim_implies_runner` with different argument order. `testing_sound_and_complete` is `observational_refinement_equiv`. `bug_detected_at_all_greater_depths` is `failure_propagates_up` renamed. `precond_bisim_weaker` is `universal_implies_preconditioned`. The 119-theorem count is somewhat inflated by these aliases. This is not a problem for correctness, but a reviewer counting theorems would notice.

## Questions for the Author(s)

- **[Q1]** The Lean `LockstepSystem` doesn't model the TypedEnv. If a GVar projection chain fails at runtime (returns `None`), the Rust precondition filter rejects the action. But the Lean `bounded_bisim` quantifies over all actions (including those with invalid projections). Does this mean the formal guarantee is vacuously true for actions that would be filtered out? If so, is `universal_implies_preconditioned` the right way to handle this, or should the Lean model track which variables are in scope?

- **[Q2]** The polynomial bridge derivation in the proc macro uses string-based type comparison (`normalize_type`). How does this handle type aliases? If a user writes `type MyResult = Result<FileHandle, FsErr>` and uses `real_return = "MyResult"`, will the derivation fail? If so, is this documented?

- **[Q3]** The `observational_refinement_equiv` theorem quantifies over `pre : List sys.ActionIdx` — an arbitrary prefix chosen by the adversary. But the actual test runner generates actions according to a strategy (which may not cover all possible prefixes). The theorem guarantees indistinguishability for ALL prefixes, but testing only checks randomly generated ones. How does this gap affect the practical interpretation of the formal guarantee?

- **[Q4]** The `dpor_swap_at` theorem requires `model_commute` at the state reached after the prefix (`model_trace_state sys pre sm`). The Rust `operations_commute` checks commutativity at the *current search state* in the linearizability tree. Are these always the same state? If the search has already committed to some operations from other branches, the state may differ.

## Minor Issues

- **[M1]** The `theory.rs` hierarchy has a formatting inconsistency: DPOR Soundness and Linearizability share a heading level, with Linearizability appearing as a subsection of DPOR Soundness (the `##` under DPOR's `#`). They should be at the same level.

- **[M2]** `derived_refines_opaque` in DerivedBridge.lean is `∀ spec, True` — it doesn't actually state anything about bridge refinement. The doc comment claims "any derived bridge refines opaque" but the theorem doesn't mention bridges at all.

- **[M3]** The `_ha_opaque` parameter in `opaque_step_then_detect` and `opaque_delayed_detection` is unused in the proof (marked with underscore). This is documented as intentional (for context), but it's unusual to carry unused hypotheses in formal proofs.

## Assessment for Publication

### ICFP Functional Pearl: **Accept**

The formalization now tells a complete, compelling story: the bridge algebra is a logical relation, bounded bisimulation captures observational refinement, the runner checks exactly the bisimulation conditions, and testing is both sound and complete. The polynomial bridge derivation as "generic programming for logical relations" is a genuine pearl insight. The concurrent testing story (DPOR, linearizability) adds depth without overwhelming the pearl narrative.

**What would push to Strong Accept:**
- Frame the pearl around the bridge algebra → logical relation → observational refinement chain
- Trim the concurrent content to a brief "extension" section
- Include a side-by-side comparison with Haskell's quickcheck-lockstep showing the bridge derivation advantage

### ESOP/ECOOP Tool Paper: **Strong Accept**

The complete toolchain (Rust library + proc macro + Lean formalization + benchmarks + 5 examples) is exceptionally well-engineered. The polynomial bridge derivation solves a real usability problem. The benchmarks provide empirical data. The formalization exceeds what any comparable testing tool offers.

**What would push to Distinguished Paper:**
- A real-world case study (not a toy kv store or file system)
- User study measuring boilerplate reduction from bridge derivation
- Comparison with other Rust testing frameworks (bolero, proptest-state-machine without lockstep)

### ISSTA/ASE: **Weak Accept**

The benchmarks are a step forward, but a testing venue still wants:
- Bug-finding results on real systems
- Coverage metrics (state space coverage vs. random testing)
- Scalability analysis beyond toy models
- Comparison with existing model-based testing tools (Jepsen, Stateright, etc.)

## Comparison to Previous Review

| Issue | Previous Status | Current Status |
|-------|----------------|----------------|
| [W1] Tautological `lockstep_test_sound` | Critical gap | **Fixed** — `runner_bounded_bisim_equiv` |
| [W3] `operations_commute` mixed bridge | Documented | Documented + formalization uses stronger check |
| [W4] No empirical evaluation | Missing | **Partially fixed** — Criterion benchmarks |
| [W5] No preconditions in formalization | Missing | **Fixed** — `Precondition.lean` |
| Sum variant mismatch rl | Missing | **Fixed** |
| DPOR soundness | Suggested | **Done** — `DPOR.lean` |
| Opaque handle detection | Suggested | **Done** — `OpaqueDetection.lean` |
| Single-step runner | Suggested | **Done** — subsumed by full runner correspondence |
| Framing as bridges-as-logical-relations | Suggested | Supported by `observational_refinement_equiv` |

**Overall trajectory**: The project has moved from "promising but incomplete" to "comprehensive and publishable." Every actionable suggestion from the previous review has been addressed. The remaining gaps (TypedEnv, probabilistic guarantees) are reasonably out of scope. The 119-theorem count is impressive, and the zero-sorry discipline is maintained throughout.

## Suggestions for Improvement (ordered by impact)

1. **Write the paper.** The formalization is ready. The pearl narrative is: bridges are logical relations, bisimulation is observational refinement, testing is sound and complete, and the bridge algebra can be derived automatically. The concurrent testing story is a strong "and also" section.

2. **Add a non-toy case study.** Testing a real concurrent Rust data structure (a lock-free queue, a concurrent HashMap, or an actor mailbox) would dramatically strengthen both the pearl and the tool paper.

3. **Fix the theory.rs hierarchy.** The DPOR/Linearizability heading levels should be consistent.

4. **Consider constructivizing `bug_localization`.** The classical proof works, but a constructive version would be more elegant.

5. **Connect `BridgeSpec` to a concrete interpretation.** Either add a dependently-typed interpretation function or remove `BridgeSpec` and just note that the existing lift theorems compose structurally.

6. **Add bridge derivation error quality tests.** Compile-fail tests (using `trybuild`) that verify the proc macro produces clear error messages when types don't match and `opaque_types` is missing.
