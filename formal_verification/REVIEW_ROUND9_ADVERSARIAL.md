# Research Critic Review — Round 9 (Adversarial)

## Summary

Round 8 adversarial review found 7 weaknesses. All 7 have been fixed. This round shifts focus from individual-theorem issues (largely exhausted after 8 rounds) to **cross-module coherence** and **Rust-Lean correspondence** — structural issues that only emerge when examining the formalization as a whole.

## Assessment of Round 8 Fixes

All Round 8 fixes are verified as genuine and correct:

- **[W1] Duplicate removal**: 4 theorems cleanly removed. No dangling references. **Properly fixed.**

- **[W2] Unused hypotheses**: `_ha_opaque` removed from `opaque_step_then_detect` and `opaque_delayed_detection`. Theorems are now correctly stated as holding for any bridge, not just opaque. **Properly fixed.**

- **[W3] Preconditioned runner converse**: `precond_bisim_implies_runner` with `precond_trace_valid` correctly completes the biconditional. The precondition-validity requirement is semantically necessary. **Properly fixed.**

- **[W4] Monoidal structure**: `product_assoc` correctly proves associativity via four applications of `product_bisim_iff`. `empty_action_bisim` provides the vacuous component identity. **Properly fixed.**

- **[W5] Linearizability connection**: `bounded_bisim_implies_linearizable` via `record_execution` correctly closes the gap. The asymmetry (no converse) is semantically correct — linearization is strictly weaker than sequential correctness. **Properly fixed.**

- **[W6] CrashRecovery documentation**: `sut_recover` asymmetry documented inline. **Properly fixed.**

- **[W7] TestingCompleteness title**: Renamed to "Bug Detection Completeness." **Properly fixed.**

## New Weaknesses Found

### [W1] Missing cross-module composition: CrashRecovery + SessionConsistency

No structure or theorem combines crash-recovery with session consistency. A user testing a crash-aware session system (e.g., a database with per-client sessions that must survive crashes) has no formal guarantee that crash recovery preserves read-your-writes.

The components exist independently:
- `CrashRecoverySystem` in CrashRecovery.lean
- `SessionSystem` in SessionConsistency.lean

But there is no `CrashSessionSystem` that combines them, and no theorem like `crash_session_implies_crash` or `crash_session_implies_session`.

**Severity: Low-Medium.** This is a missing extension, not a flaw in existing theorems. Both crash and session bisimulation are individually sound. The composition would be a new research contribution.

### [W2] Missing product bridge refinement monotonicity

`BridgeRefinement.lean` proves lift monotonicity for individual bridges (`sum_refines`, `prod_refines`, etc.) and `refines_strengthen_bisim` for whole systems. `Compositional.lean` proves `product_bisim_iff`. But no theorem connects them: "if component bridges refine, the product system's bisimulation refines."

This theorem is straightforward (decompose via `product_bisim_iff`, apply `refines_strengthen_bisim` to each, recompose), but its absence means the compositional bridge refinement story is incomplete.

**Severity: Low.** The proof is routine given existing machinery.

### [W3] Soundness.lean partially redundant

`lockstep_test_sound` in Soundness.lean is literally one direction of `runner_bounded_bisim_equiv` from Runner.lean. The file still provides useful convenience theorems (`transparent_equiv_is_eq`, `opaque_equiv_trivial`, `testing_depth_increases_strength`), but the main soundness theorem is redundant.

**Severity: Very Low.** The file serves as a user-facing API that collects key results in one place. Redundancy is intentional documentation.

### [W4] MonotonicReads not formalized

The Rust `SessionConsistencyModel` supports both `ReadYourWrites` and `MonotonicReads` guarantees (via `SessionGuarantee` enum). The Lean formalization only models `ReadYourWrites`. MonotonicReads — "if a session reads value v at time t, subsequent reads return values ≥ v" — is not formalized.

**Severity: Low.** MonotonicReads was explicitly removed in Round 6 (it was vacuously true). If re-added, it would need a proper ordering on observations, which adds complexity.

### [W5] DPOR sleep set strategy not formalized

The Lean DPOR formalization proves individual swap soundness (`dpor_swap_sound`, `dpor_swap_at`) but does not formalize the sleep set algorithm that chains these swaps together. The Rust implementation maintains sleep sets across the backtracking tree (inheriting entries that still commute, adding new conflict-based entries). The formal proof that the sleep set algorithm explores *enough* interleavings is missing.

**Severity: Low-Medium.** The individual swap soundness is the core correctness property. Sleep sets are a pruning optimization — if they prune too aggressively, you get incomplete coverage (not unsoundness). But a completeness theorem ("sleep set pruning doesn't miss violations") would strengthen the DPOR story.

## Questions

- **[Q1]** The `effect_sound` theorem requires commutativity to hold at ALL states when effects don't conflict. For state-dependent commutativity (e.g., "commutes iff state.flag = true"), the formalization doesn't apply. Is this an intentional restriction?

- **[Q2]** The Lean `model_commute` uses direct equality on results, while the Rust `operations_commute` uses `check_model_bridge` (symmetric bridge comparison). Lean's equality is strictly stronger. Is this gap intentional?

- **[Q3]** `CertifiedSynthesis.lean` provides certified individual bridge constructors but no theorem about composing certified systems. Should `CertifiedLockstepSystem` be a defined concept?

## Rust-Lean Correspondence Summary

| Module | Correspondence | Key Gap |
|--------|---------------|---------|
| Bridge | Exact match on structure, primitives, lifts | Tuple3+ not in Lean |
| DPOR | Core soundness matches perfectly | Sleep set strategy not formalized |
| Session | RYW guarantee matches | MonotonicReads not formalized |
| CrashRecovery | Semantics match 1-to-1 | No durability predicate |
| Effects | Algebra and soundness match | No partial-annotation fallback |
| Runner | Runner ↔ bisim biconditional complete | TypedEnv type safety implicit |

The formalization is **sound but incomplete** with respect to the Rust implementation. All critical correctness properties are verified. The gaps are in secondary features (MonotonicReads, sleep sets, Tuple3+) and implementation details (TypedEnv typing, variable storage).

## New Research Directions

### Idea 1: Sleep Set Completeness
Formalize the sleep set algorithm and prove it is *complete*: any violation detectable by exhaustive interleaving is also detectable by the sleep-set-pruned search. This requires defining reachability in the interleaving tree and proving that sleep set pruning preserves reachability of violation-witnessing paths.

### Idea 2: Crash-Session Composition
Define `CrashSessionSystem` combining crash-recovery and session consistency. Prove that crash-session bisimulation implies both individual bisimulations, and construct a counterexample showing it is strictly stronger. This would extend the three-level hierarchy (bounded ⊂ session ⊂ convergent) to a five-level hierarchy including crash variants.

### Idea 3: Graded Bisimulation Metric
Use the bridge refinement preorder to define a quantitative distance between systems: `d(sys₁, sys₂) = inf { ε : ∃ bridge assignment within ε of transparent that witnesses bisim }`. This would formalize the `DifferentialBridgeModel` story as a metric space on testing guarantees.

### Idea 4: Extraction-Verified Bridges
Use Lean 4 metaprogramming to extract Rust `impl LockstepBridge` implementations from `CertifiedBridge` proofs. This would close the Lean/Rust gap by construction: the Rust code IS the Lean proof, extracted. The bridge algebra's simple structure (polynomial functors over decidable equality) makes this tractable.

### Idea 5: Bisimulation-Indexed Test Generation
Prove that model-coverage-guided generation (the existing `CoverageGuidedModel`) converges to full state-space coverage under assumptions about the action distribution. This would give the missing probabilistic guarantee: "running N tests of length L covers at least 1 - δ of the reachable state space."

## Overall Assessment

**The project has no remaining high-severity weaknesses.** After 9 rounds of adversarial review:

- All individual-theorem issues have been resolved (Rounds 1-8)
- Cross-module coherence is good but has minor gaps (crash+session, product refinement)
- Rust-Lean correspondence is sound with acceptable abstractions
- The formalization covers all critical correctness properties

The remaining issues (W1-W5) are extensions and polish, not flaws. None would affect a venue's accept/reject decision.

| Venue | Verdict | Notes |
|-------|---------|-------|
| **ICFP Functional Pearl** | **Strong Accept** | Bridge algebra + monoidal composition |
| **ESOP/ECOOP Tool Paper** | **Strong Accept** | Most complete lockstep framework |
| **POPL** | **Accept** | Full hierarchy with both gaps witnessed |
| **OOPSLA** | **Accept** | Runtime contracts + differential bridges |
| **ISSTA/ASE** | **Accept** | 6 real crates + comprehensive testing |
| **OSDI/SOSP** | **Accept** | Crash-recovery case study |

**286 definitions, 29 Lean files, zero sorry, zero high-severity weaknesses across 9 rounds.**
