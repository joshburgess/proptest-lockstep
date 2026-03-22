# Assessment of the Adversarial Critique

Reviewing each point from the Round 6 adversarial critique against the actual code.

## [W1] session_bisim is vacuous

**VALID — should fix. This is a real problem.**

Verified: `session_bisim` at line 91-100 of `SessionConsistency.lean` is:
```lean
| n + 1, sm, ss => ∀ (a : sys.ActionIdx),
    session_bisim sys n (sys.step_model a sm).1 (sys.step_sut a ss).1
```

This is exactly `bounded_bisim` with the bridge check removed. It does NOT use `read_your_writes`, `monotonic_reads`, `SessionHistory`, `session_of`, `read_obs`, or `write_obs`. Those definitions exist (lines 49-80) but appear in ZERO theorems.

The doc comment says "requires that session guarantees are maintained for each session's observations" — but the definition doesn't check session guarantees at all. `bounded_implies_session` is trivially true because session_bisim is strictly weaker (drops bridge check, adds nothing).

**Severity: High.** This means the session consistency formalization doesn't formalize session consistency. It formalizes "bounded bisimulation without bridge checks," which is a different (and less interesting) concept.

**Fix:** Redefine `session_bisim` to thread per-session histories and require `read_your_writes` for each session's read operations. This is substantial work but necessary for the claim to be honest.

## [W2] monotonic_reads is trivially true

**VALID — should fix.**

Verified: `obs = v ∨ True` reduces to `True` in Lean's logic. The definition accepts any observation as "monotonically consistent," which is vacuous.

**Severity: Medium.** This is a broken definition, but since `monotonic_reads` isn't used in any theorem, it's currently harmless. It becomes High severity if/when `session_bisim` is fixed to actually use it.

**Fix:** Either (a) define a proper version ordering on observations and check monotonicity against it, or (b) remove `monotonic_reads` and note it requires a version ordering that's domain-specific.

## [W3] synthesis_compositional is True := trivial

**VALID — should fix, but low priority.**

Verified: The theorem proves `True`. The doc comment claims it proves compositionality. This is misleading.

**Severity: Low.** The actual compositionality IS proved — by the individual `certified_*_sound` theorems. The `synthesis_compositional` theorem is just a documentation placeholder, not a load-bearing proof. But a reviewer would rightfully object to a theorem that proves `True` with a doc comment claiming it proves something else.

**Fix:** Either (a) state and prove the actual compositional property (e.g., "if `cb1` and `cb2` are certified, then `certify_sum cb1 cb2` is certified"), or (b) remove the theorem and replace with a comment explaining that compositionality follows from the individual theorems.

## [W4] CertifiedBridge has no proof obligation

**PARTIALLY VALID — worth noting but not a blocker.**

Verified: `CertifiedBridge R M` is `{ bridge : Bridge R M }`. You CAN construct one without `certify_*`.

However, the `certify_*` functions are the INTENDED API, and the soundness theorems are proved FOR those functions. The lack of enforcement is a design choice — in Lean, you could enforce it with a private constructor or an opaque type, but the current approach is simpler.

**Severity: Low.** In a paper, you'd say "certified bridges are constructed via the `certify_*` API, which guarantees soundness" — the lack of runtime enforcement doesn't invalidate the proofs. A reviewer might note it but wouldn't reject over it.

**Fix:** Make the `CertifiedBridge` constructor private and only expose the `certify_*` functions. Or add a proof field.

## [W5] Consistency hierarchy not proved strict

**VALID — should fix for a POPL paper.**

Verified: `bounded_implies_session` and `bounded_implies_convergent` exist, but there are no strictness witnesses (systems where the weaker holds but the stronger doesn't).

**Severity: Medium for ICFP pearl (doesn't claim hierarchy), High for POPL (the hierarchy IS the claim).**

Without strictness, a reader might worry that bounded_bisim = session_bisim = convergent_bisim for all systems. The implications could be equivalences for all we've proved.

**Fix:** Construct concrete `LockstepSystem` instances witnessing each gap. The `evmap` Rust example demonstrates this empirically (passes EC, fails linearizability), but there's no Lean counterexample.

## [W8] Missing session_implies_convergent

**VALID — should fix.**

Verified: `grep` confirms no theorem connects session_bisim to convergent_bisim. The README claims `linearizability ⟹ session ⟹ eventual` but only two of three edges are proved.

**Severity: Medium.** The missing edge makes the hierarchy diagram incomplete. However, since session_bisim is currently vacuous (W1), this edge is currently meaningless anyway — fixing W1 first would make W8 meaningful.

**Fix:** After fixing W1, prove `session_bisim n sm ss → convergent_bisim n sm ss` under appropriate conditions.

## [W9] Environment formalization is an island

**VALID but LOW PRIORITY — acknowledge in paper.**

Verified: `env_bounded_bisim` is only used within `Environment.lean`. No extension uses it.

**Severity: Low.** The environment formalization proves the key theorem (`env_runner_bounded_bisim_equiv`) — that's its purpose. Lifting every extension to use `EnvLockstepSystem` would be a significant amount of work with limited payoff: the environment-free versions are sound overapproximations (the `lift_bisim_equiv` theorem shows this).

**Fix for paper:** Acknowledge this as a design choice: "The extensions are formalized against `LockstepSystem` (environment-free), which `lift_bisim_equiv` shows is a conservative abstraction of the environment-aware `EnvLockstepSystem`." No code change needed.

## Summary: What to fix

| Issue | Verdict | Priority | Effort |
|-------|---------|----------|--------|
| [W1] session_bisim vacuous | **VALID — fix** | High | High (substantial redesign) |
| [W2] monotonic_reads trivial | **VALID — fix** | Medium | Low (fix or remove) |
| [W3] synthesis_compositional | **VALID — fix** | Low | Low (remove or restate) |
| [W4] CertifiedBridge no enforcement | **Partially valid** | Low | Low |
| [W5] Hierarchy not strict | **VALID — fix for POPL** | Medium | Medium (construct counterexamples) |
| [W8] Missing session→convergent | **VALID — fix** | Medium | Low (after W1 is fixed) |
| [W9] Environment is island | **Valid but low priority** | Low | Acknowledge in paper |

**Recommended action order:**
1. Fix W1 (session_bisim) — highest priority, most impactful
2. Fix W2 (monotonic_reads) — comes for free with W1
3. Fix W3 (remove synthesis_compositional True := trivial)
4. Fix W5 (strictness counterexamples) — important for POPL
5. Fix W8 (session→convergent edge) — after W1 is meaningful
6. Acknowledge W9 in paper documentation
7. Optionally fix W4 (private constructor)
