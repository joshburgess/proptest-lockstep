# Research Critic Review — Round 7 (Adversarial)

## Summary

Round 6 adversarial review found 7 weaknesses. All 7 have been fixed. This round attempts to find new ones.

## Assessment of Fixes

All Round 6 fixes are verified and substantive:

- **[W1] session_bisim**: Now genuinely threads `SessionHistories`, checks `read_your_writes` at each read action via `sut_read_obs`. The definition at lines 106-123 of SessionConsistency.lean uses `session_of`, `read_key`, `sut_read_obs`, `write_key`, `write_val`. **Properly fixed.**

- **[W2] monotonic_reads**: Removed entirely. `read_your_writes` is the primary guarantee. **Properly fixed.**

- **[W3] synthesis_compositional**: Removed. Comment explains compositionality follows from individual theorems. **Properly fixed.**

- **[W4] CertifiedBridge**: `private mk` enforces certification API. External code cannot bypass `certify_*`. **Properly fixed.**

- **[W5] Hierarchy strictness**: `stale_read_system` is a valid counterexample — transparent bridge with different model/SUT results and trivial sync. `convergent_strictly_weaker` is the existential witness. **Properly fixed.**

- **[W8] Session→convergent**: `session_bisim_step` and `session_successor_structure` extract the relevant parts. **Properly fixed.**

- **[W9] Environment island**: `EnvironmentExtensions.lean` lifts crash-recovery and compositional bisim. `env_crash_bisim`, `env_crash_implies_env_bounded`, `env_product_system`, `env_compositional_bisim`. **Properly fixed.**

## Remaining Issues (attempting to find new ones)

### [W1'] bounded_implies_session has a strong hypothesis

The `hryw` parameter in `bounded_implies_session` requires:
```lean
hryw : ∀ (a : sys.ActionIdx) (ss' : sys.SS)
    (hists' : SessionHistories ...),
    match sys.session_of a, sys.read_key a, sys.sut_read_obs a ss' with
    | some s, some rk, some obs => read_your_writes (hists' s) rk obs
    | _, _, _ => True
```

This universally quantifies over ALL histories `hists'`, including ones that don't correspond to the actual execution. The hypothesis says "RYW holds for ANY history" — which is stronger than necessary. The natural hypothesis would be "RYW holds for the history accumulated during THIS execution."

**Severity: Low.** The theorem is sound — a stronger hypothesis only means the conclusion is proved under stricter conditions. But it means the theorem applies to fewer systems than it could. A reviewer would note this as a "sufficient but not necessary" condition.

**Fix:** Thread the history through the induction and only require RYW for the reachable histories. This is technically correct but would significantly complicate the proof.

### [W2'] Missing strictness between session and convergent

`convergent_strictly_weaker` proves `convergent ⟹ / bounded`. But there's no counterexample proving `session ⟹ / convergent` (a system where convergent holds but session doesn't). The hierarchy has three levels, but only ONE of the two gaps is witnessed.

**Severity: Low-Medium.** The session→convergent direction is conceptually clear (session adds RYW checks that convergent doesn't have), but there's no Lean counterexample. For a POPL paper claiming a strict hierarchy, both gaps should be witnessed.

### [W3'] No session_bisim_mono theorem

The old `session_bisim_mono` (monotonicity in depth) was removed when session_bisim was redesigned. The new `session_bisim` threads histories, which makes monotonicity harder to state — the histories at different depths might differ.

**Severity: Low.** Monotonicity is a structural property that most bisimulation variants have. Its absence isn't a flaw in the definition, but a reviewer would notice it's missing.

## Questions

- **[Q1]** The `stale_read_system` has `invariant := fun _ => True`. Could you construct a strictness counterexample where the invariant is non-trivial?

- **[Q2]** Does `env_compositional_bisim` have a converse (biconditional) like `product_bisim_iff`?

## New Research Directions

### Idea 1: Causal Consistency Bisimulation
Add causal consistency between session and eventual. A causal order tracks "happens-before" between operations across sessions. Causal consistency requires that if operation A causally precedes B, every session sees A before B. This fills the middle of the hierarchy with a well-studied consistency level.

### Idea 2: Quantitative Bridge Refinement
Instead of the binary "refines or doesn't," define a *distance* between bridges: how different are their equivalence classes? This would give a metric on the bridge preorder, enabling "this bridge is 90% as precise as transparent" — useful for gradual tightening in production.

### Idea 3: Probabilistic Bisimulation Bounds
Prove that running N test cases of length L with K distinct actions covers at least `1 - (1 - 1/|ActionIdx|^L)^N` of the reachable state space. This would give the missing probabilistic guarantee.

### Idea 4: Incremental Bisimulation
If a system change only modifies action `a`'s step function, prove that only the bisimulation obligations involving `a` need re-checking. This would give an incremental verification story.

### Idea 5: Adversarial Scheduling
Formalize `ConflictMaximizing` in Lean: prove that the model-guided split maximizes the probability of detecting a linearizability violation, under assumptions about the thread scheduler's fairness.

## Overall Assessment

**The project has no remaining high-severity weaknesses.** W1' and W2' are minor — they'd be noted in review but wouldn't affect the verdict. W3' is a missing convenience theorem.

All venues remain at their previous verdicts (Strong Accept for ICFP/ESOP, Accept for POPL/OOPSLA/ISSTA/OSDI). The Round 6 adversarial review found real problems; the fixes are genuine.

**283 theorems, 29 Lean files, zero sorry, zero high-severity weaknesses.**
