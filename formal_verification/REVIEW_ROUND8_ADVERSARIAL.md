# Research Critic Review — Round 8 (Adversarial)

## Summary

Round 7 adversarial review found 3 low-severity weaknesses (W1', W2', W3'). All 3 have been fixed. This round performs a comprehensive sweep across all 29 Lean files, 284 definitions, looking for structural issues: duplicates, tautologies, missing biconditionals, abstraction mismatches, and gaps between the Lean formalization and the Rust implementation.

## Assessment of Round 7 Fixes

All Round 7 fixes are verified and substantive:

- **[W1'] bounded_implies_session**: Now conditions `hryw` on `bridge_equiv` holding — strictly weaker hypothesis that applies to more systems. The bridge guarantee is the natural precondition. **Properly fixed.**

- **[W2'] session↛convergent strictness**: `session_strictly_stronger` proves the gap via `ryw_violation` counterexample. The system has identical transitions in both `ryw_violation_session` and `ryw_violation_eventual`; the SUT always returns stale data on reads (violating RYW) but sync trivially agrees (satisfying convergent_bisim at all depths). Both hierarchy gaps are now witnessed. **Properly fixed.**

- **[W3'] session_bisim_mono**: Correctly proves monotonicity for the redesigned `session_bisim` with threaded histories. Induction handles history threading cleanly. **Properly fixed.**

## New Weaknesses Found

### [W1] Duplicate theorems (4 instances)

Four pairs of theorems are exact duplicates or trivial aliases:

1. **`opaque_detection_tight` ≡ `opaque_needs_depth_2`** (BridgeDepth.lean:76-85 vs 43-52): Identical signatures, identical proofs (both delegate to `opaque_depth_sensitivity`).

2. **`sequential_is_linearizable` ≡ `single_branch_linearizable`** (Linearizability.lean:49-53 vs 94-98): `single_branch_linearizable` literally calls `sequential_is_linearizable`. Same types, same meaning.

3. **`tensor_readonly_step` ≡ `tensor_bisim_step`** (TensorProduct.lean:162-170 vs 177-184): Identical proofs (`h.2 a`), only argument order differs. The "readonly" name is misleading — the theorem doesn't use a read-only hypothesis.

4. **`regression_witnessed`** (Regression.lean:35-39): Proof is literally `h` — it restates the definition of `is_regression` as a theorem with zero additional content.

**Severity: Low.** These are cosmetic clutter, not soundness issues. A reviewer would flag them as padding the theorem count (284 → ~280 after deduplication).

**Fix:** Remove `opaque_detection_tight`, `single_branch_linearizable`, `tensor_readonly_step`, and `regression_witnessed`. Alternatively, if the aliases serve documentation purposes, add comments explaining why they exist.

### [W2] Unused hypotheses in OpaqueDetection.lean

Two theorems carry `_ha_opaque` parameters (underscore-prefixed) that are explicitly unused:

- `opaque_step_then_detect` (line 78): The opaque hypothesis on action `a` is documented as "not needed for the proof" but "included to document the intended use case."
- `opaque_delayed_detection` (line 103): Same pattern.

**Severity: Very Low.** The comments justify this design choice. A reviewer might note the theorems are more general than their names suggest (they hold for any bridge on `a`, not just opaque ones).

### [W3] Missing precond_bisim_implies_runner converse

`Precondition.lean` proves `precond_runner_implies_bisim` (runner passes on all valid traces → precond bisim) but lacks the converse direction. The full correspondence `precond_runner_bounded_bisim_equiv` (biconditional) is missing — unlike the unpreconditioned case where `runner_bounded_bisim_equiv` provides both directions.

**Severity: Low-Medium.** The forward direction (runner → bisim) is the one needed for soundness. The converse (bisim → runner) would complete the analogy with `runner_bounded_bisim_equiv` and is needed for completeness claims.

**Fix:** Add `precond_bisim_implies_runner` and `precond_runner_bounded_bisim_equiv`.

### [W4] No product_bisim associativity or identity

`Compositional.lean` proves the biconditional `product_bisim_iff` (product bisim ↔ both components), which is excellent. But there is no associativity theorem for `product_system (product_system sys1 sys2) sys3` ≅ `product_system sys1 (product_system sys2 sys3)`, and no identity element (trivial system that acts as neutral for product composition).

**Severity: Low.** The biconditional suffices for most practical purposes — associativity follows informally from the iff. For an algebra-focused paper (ICFP pearl), a reviewer would ask for the full monoidal structure.

### [W5] Linearizability.lean disconnected from bounded_bisim

`is_linearizable` is defined and has algebraic properties (swap, permutation invariance), but no theorem connects it to `bounded_bisim` from `Lockstep.lean`. The conceptual bridge — "if all linearizations of a concurrent execution satisfy bounded_bisim, the concurrent execution is correct" — is informal. `Linearizability.lean` imports `DPOR.lean` but never uses `model_commute` or the DPOR swap theorems directly in its own theorems.

**Severity: Medium.** The Rust implementation connects these (the concurrent runner checks linearizability via bounded_bisim), but the Lean formalization doesn't state the connecting theorem. A POPL reviewer would consider this the biggest remaining gap in the formalization.

**Fix:** Add a theorem like:
```lean
theorem linearizable_implies_concurrent_correct :
    is_linearizable sys records sm →
    ∃ perm, linearization_check sys perm sm
```
(which already exists implicitly in the definition) and a theorem connecting `linearization_check` to `bounded_bisim` on the sequential execution.

### [W6] CrashRecovery.lean: sut_recover takes no checkpoint

`CrashRecoverySystem.sut_recover : SS → SS` recovers from the SUT's own state, not from the model's checkpoint. The model side uses `model_recover : DS → SM` (from a checkpoint), but the SUT side recovers from its full state. This is intentional (the SUT must self-recover from its persisted state, not from the model's view), but no theorem states the key property: "after recovery, the model and SUT are back in the bisimulation."

**Severity: Low.** `crash_recovery_preserves` proves exactly this property (`crash_bisim(n+1) → crash_bisim(n)` on recovered states). The design choice is correct — the SUT doesn't have access to the model's checkpoint. The only issue is that the docstring could be clearer about why this asymmetry is intentional.

### [W7] TestingCompleteness.lean title oversells scope

The file title and docstring say "Testing Completeness," but the main theorem `testing_completeness` is actually the *contrapositive of soundness*: "if observations differ, bisimulation fails." True completeness would be: "testing at depth n detects all bugs that manifest within n steps." The file proves the negative direction but not the positive algorithmic guarantee.

**Severity: Low.** The theorem IS correct and useful. The naming just oversells it. `bug_localization` uses `Classical.byContradiction`, which is justified since `ActionIdx` is not assumed finite.

## Questions

- **[Q1]** Would it be worth proving the full monoidal structure for product composition (associativity + identity)? This would strengthen the ICFP pearl angle significantly.

- **[Q2]** The `effect_sound` theorem in EffectLattice.lean requires commutativity to hold at ALL states when effects don't conflict. Is this intentional, or should it be restricted to reachable states? For partial effect algebras (where commutativity is state-dependent), the current formulation is too strong.

- **[Q3]** The CertificateHash.lean proofs use `native_decide` for hash verification. This relies on Lean's runtime computation agreeing with the expected constants. Is there a way to verify the hashes through pure computation instead?

## Abstraction Mismatches Between Lean and Rust

These are structural observations, not weaknesses per se:

1. **TypedEnv gap**: The Rust `TypedEnv` uses `Box<dyn Any + Send>` with runtime type checking. The Lean `Environment.lean` uses an abstract `Env` type with no typing discipline. The type safety of variable environments is not formalized.

2. **Determinism assumption**: The Lean formalization assumes `step_model` and `step_sut` are pure functions. The Rust `LockstepSut` re-runs the model per step. No theorem states that re-running the model produces identical results (though this follows from Rust's deterministic semantics for the types involved).

3. **Bridge observation decidability**: The Lean `Bridge` structure carries `dec_eq : DecidableEq Observed`. In Rust, this is `PartialEq` on the observed type. The Lean formalization correctly captures this requirement.

4. **Sleep set not formalized**: The DPOR formalization proves individual swap soundness but doesn't formalize the sleep set algorithm (construction, maintenance, completeness). The Rust implementation maintains sleep sets across the backtracking tree.

## New Research Directions

### Idea 1: Monoidal Category of Lockstep Systems
Prove that `LockstepSystem` with `product_system` as tensor product, a trivial system as unit, and `bridge_refines` as morphisms forms a monoidal category. The biconditional `product_bisim_iff` would be the key lemma. This gives a categorical semantics for compositional testing — composing systems is functorial.

### Idea 2: Trace Equivalence Characterization
Prove that `bounded_bisim` at depth n is equivalent to trace equivalence up to length n (equal observations on all traces of length ≤ n). The forward direction is `observational_refinement_equiv`; the reverse needs a trace-based characterization. This would connect lockstep bisimulation to the standard process algebra notion.

### Idea 3: Incremental Bisimulation Under System Modification
If a system change only modifies action `a`'s step function, prove that only bisimulation obligations involving `a` need re-checking. The current `Regression.lean` defines when a regression exists but doesn't characterize *which* obligations changed. An incremental theorem would give `O(1)` re-verification for single-action changes.

### Idea 4: Quantitative Bridge Distance
Define a metric on bridges: `bridge_distance(b1, b2) = |{(r,m) : b1(r,m) ≠ b2(r,m)}|` (for finite types). Prove that closer bridges give closer bisimulation guarantees. This would formalize the `DifferentialBridgeModel` story: "this bridge is ε-close to transparent."

### Idea 5: Inductive Invariant Characterization
Define `inductive_invariant(P) := ∀ sm a, P sm → P (step_model a sm).1` and prove that if `P` is inductive and holds initially, it holds everywhere along any trace. The current `Invariant.lean` checks invariants at each step but doesn't exploit inductiveness for one-shot verification. An inductive invariant theorem would reduce the checking cost from O(n) per trace to O(1) per system.

## Overall Assessment

**The project has no remaining high-severity weaknesses.** The issues found are:
- 4 duplicate theorems (cosmetic, ~1.4% of total)
- 1 missing converse (preconditioned runner biconditional)
- 1 disconnected module (linearizability↔bounded_bisim)
- Naming/documentation nits

The Round 7 fixes are genuine and correctly implemented. The hierarchy now has both gaps witnessed by Lean counterexamples. The `bounded_implies_session` hypothesis is properly weakened.

All venues remain at their previous verdicts:

| Venue | Verdict | Notes |
|-------|---------|-------|
| **ICFP Functional Pearl** | **Strong Accept** | Bridge algebra + monoidal composition story |
| **ESOP/ECOOP Tool Paper** | **Strong Accept** | Most complete lockstep framework in any language |
| **POPL** | **Accept** | Consistency hierarchy with both gaps witnessed |
| **OOPSLA** | **Accept** | Runtime contracts + differential bridges |
| **ISSTA/ASE** | **Accept** | 6 real crates + bug detection + benchmarks |
| **OSDI/SOSP** | **Accept** | sled crash-recovery case study |

**~280 non-duplicate theorems, 29 Lean files, zero sorry, zero high-severity weaknesses.**
