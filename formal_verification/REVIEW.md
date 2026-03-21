# Research Critic Review — Lean 4 Formal Verification

## Verification Report

All previous issues confirmed fixed:

| Fix | Status |
|-----|--------|
| List bridge added | **Confirmed** — `listBridge`, `list_preserves_nil`, `list_preserves_cons`, `list_equiv_length`, all machine-checked |
| theory.rs rewritten | **Confirmed** — no `RefinementCertificate`, no `BridgeFunctor`, theorem names match Lean exactly, "What Is NOT Formalized" section is honest |
| Zero sorry | **Confirmed** |

## Assessment for Publication

**Workshop paper (e.g., TFP, Haskell Symposium experience report): Accept.** The formalization establishes that the bridge algebra is a logical relation closed under sum, product, option, and list — with machine-checked proofs of the fundamental theorem for each. The bounded bisimulation definition and its monotonicity are correct and non-trivial. The honest documentation of what's NOT formalized (runner, preconditions, probabilistic guarantees) strengthens credibility.

**Functional pearl (ICFP): Borderline.** The algebraic properties are clean but the gap to the runner is significant. A reviewer would say: "The interesting claim is that lockstep testing implies observational refinement, but the proof stops at the algebra — the connection to the test runner is informal." To upgrade to a strong pearl submission, you'd need either: (a) formalize single-step runner behavior (model the `apply` function in Lean and prove it establishes `bounded_bisim 1`), or (b) frame the paper around the bridge algebra itself as the contribution (a "bridges as logical relations" pearl), with the bisimulation as supporting evidence.

**The library + formalization together are stronger than either alone.** The Rust artifact demonstrates practical utility (64 unit tests, 4 examples, concurrent testing, DPOR, linearizability). The Lean artifact demonstrates theoretical soundness (22+ machine-checked theorems, zero sorry). No other property-based testing framework has both.

## Detailed Review

### Strengths

- **[S1] The Bridge structure faithfully corresponds to the Rust `LockstepBridge` trait.** The Lean `Bridge` has `Observed`, `observe_real`, `observe_model` — exactly matching the Rust trait's associated type and methods. The `bridge_equiv` definition (`observe_real r = observe_model m`) captures what `LockstepBridge::check` computes.

- **[S2] The fundamental theorem is correctly stated and proved.** Each bridge lift (sum, product, option, list) preserves equivalence: if components are bridge-equivalent, the lifted values are bridge-equivalent. These are the key lemmas for a logical relation.

- **[S3] The bounded bisimulation definition captures what lockstep testing actually does.** `bounded_bisim sys (n+1) sm ss` says: for all actions, the results are bridge-equivalent AND the successor states are in the depth-n bisimulation. This exactly mirrors the `LockstepSut::apply` method.

- **[S4] The monotonicity proof is non-trivial and correct.** `bounded_bisim_mono` proves that testing at depth m ≥ n implies the bisimulation at depth n.

### Weaknesses (Acknowledged)

- **[W1] `lockstep_test_sound` is tautological** — the real soundness theorem connecting the runner to the bisimulation is not formalized. Acknowledged in theory.rs.

- **[W2] `lockstep_bisim` (coinductive) is defined but not used** — expected, since full bisimulation can't be established by testing.

- **[W3] No preconditions or TypedEnv** — the formalization quantifies over ALL actions, which is conservative (stronger than what tests check).

### What Would Strengthen It

1. **Formalize single-step runner behavior** — model the `apply` function in Lean and prove it establishes `bounded_bisim 1`.
2. **Frame as "bridges as logical relations" pearl** — the bridge algebra itself is the contribution, bisimulation is supporting evidence.
3. **DPOR soundness formalization** — prove that commuting operations can be reordered without affecting the bisimulation.
4. **Opaque handle detection theorem** — formalize that a wrong opaque handle is detected when used later (bridge equivalence fails at depth n+k).

### Theorem Inventory

**Bridge.lean (12 theorems):**
- `transparent_refl`, `opaqueBridge_always`
- `sum_preserves_ok`, `sum_preserves_err`, `sum_variant_mismatch_lr`
- `prod_preserves`, `prod_equiv_iff`
- `option_preserves_some`, `option_preserves_none`
- `list_preserves_nil`, `list_preserves_cons`, `list_equiv_length`

**Lockstep.lean (5 theorems):**
- `bounded_bisim_zero`, `bounded_bisim_mono`, `bounded_bisim_mono'`
- `bisim_implies_bounded`, `single_step_bisim`

**Soundness.lean (7 theorems):**
- `lockstep_test_sound`, `deeper_test_stronger`, `testing_depth_increases_strength`
- `transparent_equiv_is_eq`, `opaque_equiv_trivial`
- `sum_bridge_sound_ok`, `sum_bridge_sound_err`
- `sum_bridge_variant_mismatch_lr`, `sum_bridge_variant_mismatch_rl`
- `prod_bridge_sound`

All machine-checked, zero `sorry`s, Lean 4.28.0.
