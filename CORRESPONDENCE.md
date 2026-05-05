# Lean ↔ Rust Correspondence

This document maps every Lean theorem to the Rust function or construct it
is claimed to model. It exists to make the **trust boundary** of this
project explicit: what is machine-checked, and what is correlated by
design and inspection.

## Scope statement

The Lean development in `metatheory/` is **mechanized
metatheory**, not implementation verification. The theorems prove
properties of an abstract specification of lockstep testing (bridges,
bisimulation, runner, linearizability, etc.). The Rust implementation
is designed to mirror that specification, but no machine-checked link
exists between Lean definitions and Rust source.

This is the same model used by POPLmark, most ICFP artifacts with
formalizations, and the original `quickcheck-lockstep` (which has no
formalization at all). It is strictly stronger than "tests pass" and
strictly weaker than "every line of Rust is verified" (cf. RustBelt,
CompCert, seL4).

## Counts

| | Count |
|---|---|
| Lean files | 34 |
| Theorems / lemmas | 236 |
| Definitions / structures / inductives / classes | 136 |
| `sorry` axioms | 0 |

(Run `cd metatheory && lake build` to re-check.)

## Theorem → Rust correspondence

### Bridge algebra

| Lean construct | Rust construct | Lean file |
|---|---|---|
| `Bridge` structure | `LockstepBridge` trait | `Bridge.lean` |
| `bridge_equiv` | `LockstepBridge::check` returning `Ok(())` | `Bridge.lean` |
| `transparent T` | `Transparent<T>` | `Bridge.lean` |
| `opaqueBridge R M` | `Opaque<R, M>` | `Bridge.lean` |
| `sumBridge` | `ResultBridge<OkB, ErrB>` | `Bridge.lean` |
| `prodBridge` | `TupleBridge<AB, BB>` | `Bridge.lean` |
| `optionBridge` | `OptionBridge<B>` | `Bridge.lean` |
| `listBridge` | `VecBridge<B>` | `Bridge.lean` |
| `bridge_equiv_decidable` | `Self::Observed: PartialEq` (weakening) | `Bridge.lean` |

### Bridge refinement

| Lean construct | Rust construct | Lean file |
|---|---|---|
| `bridge_refines` | conceptual: "B1 is finer than B2" | `BridgeRefinement.lean` |
| `refines_strengthen_bisim` | `differential.rs` differential testing | `BridgeRefinement.lean` |
| `derivation_monotone_*` | proc macro's polynomial bridge derivation | `DerivedBridge.lean` |

### Runner and bisimulation

| Lean construct | Rust construct | Lean file |
|---|---|---|
| `LockstepSystem` | `LockstepModel` trait + `LockstepSut` | `Lockstep.lean` |
| `runner_passes` | `LockstepSut::apply` (the apply loop) | `Runner.lean` |
| `bounded_bisim n` | implicit invariant of an `n`-step passing run | `Lockstep.lean` |
| `runner_bounded_bisim_equiv` | runner correctness theorem (no direct Rust counterpart) | `Runner.lean` |
| `bounded_bisim_mono` | depth-monotonicity of the runner | `Lockstep.lean` |

### Observational refinement

| Lean construct | Rust construct | Lean file |
|---|---|---|
| `observational_refinement` | the guarantee a passing test provides | `ObservationalRefinement.lean` |
| `observational_refinement_equiv` | (no Rust counterpart; pure metatheory) | `ObservationalRefinement.lean` |
| `bisim_along_trace` | invariant maintained throughout `apply` | `ObservationalRefinement.lean` |

### Testing completeness

| Lean construct | Rust construct | Lean file |
|---|---|---|
| `testing_completeness` | "if the SUT diverges from the model, depth `n+1` catches it" | `TestingCompleteness.lean` |
| `bug_localization` | `shrinking.rs` bisimulation-guided shrinker | `TestingCompleteness.lean` |
| `immediate_bug` | bridge check failure at current step | `TestingCompleteness.lean` |

### Linearizability and DPOR

| Lean construct | Rust construct | Lean file |
|---|---|---|
| `is_linearizable` | `concurrent.rs::check_linearizability` | `Linearizability.lean` |
| `linearization_check` | per-permutation validation inside the search | `DPOR.lean` |
| `model_commute` | `concurrent.rs::operations_commute` | `DPOR.lean` |
| `dpor_swap_sound` | DPOR pruning soundness | `DPOR.lean` |
| `dpor_swap_iff` | (not used by Rust; biconditional is metatheory only) | `DPOR.lean` |

### Effect lattice

| Lean construct | Rust construct | Lean file |
|---|---|---|
| `EffectAlgebra` | `effects.rs::ConflictAlgebra` | `EffectLattice.lean` |
| `effect_sound` | obligation on user effect annotations | `EffectLattice.lean` |
| `effect_dpor_sound` | `effects.rs::EffectModel` integration with DPOR | `EffectLattice.lean` |
| `RWEffect` / `rw_conflicts` | standard read/write effect helpers | `EffectLattice.lean` |

### Opaque handle detection

| Lean construct | Rust construct | Lean file |
|---|---|---|
| `opaque_step_then_detect` | guarantee of `Opaque<R, M>` over multi-step traces | `OpaqueDetection.lean` |
| `opaque_delayed_detection` | k-step delayed detection | `OpaqueDetection.lean` |
| `opaque_depth_sensitivity` | proves deeper testing is necessary, not just sufficient | `OpaqueDetection.lean` |

### Crash recovery

| Lean construct | Rust construct | Lean file |
|---|---|---|
| `crash_bisim` | `crash_recovery.rs::CrashRecoveryModel` semantics | `CrashRecovery.lean` |
| `crash_recovery_preserves` | invariant of the crash injection harness | `CrashRecovery.lean` |
| `crash_then_bounded_bisim` | normal lockstep continues to apply post-recovery | `CrashRecovery.lean` |
| `crash_bisim_double_crash` | nested crash robustness | `CrashRecovery.lean` |

### Consistency hierarchy

| Lean construct | Rust construct | Lean file |
|---|---|---|
| `bounded_implies_session` | linearizability ⇒ session consistency | `SessionConsistency.lean` |
| `bounded_implies_convergent` | linearizability ⇒ eventual consistency | `EventualConsistency.lean` |
| `convergent_bisim_sync` | `eventual.rs::EventualConsistencyModel` sync semantics | `EventualConsistency.lean` |

### Compositional and other

| Lean construct | Rust construct | Lean file |
|---|---|---|
| `compositional_bisim` | `compositional.rs::CompositionalModel` | `Compositional.lean` |
| `spec_sound` / `spec_dpor_sound` | `commutativity.rs::CommutativitySpecModel` | `CommutativitySpec.lean` |
| `certified_*_sound` | `certified.rs::CertifiedLockstepBridge` marker trait | `CertifiedSynthesis.lean` |
| `proj_*_preserves` | `op.rs::Op` trait + `gvar.rs::GVar` projections | `Projection.lean` |
| `env_runner_bounded_bisim_equiv` | `env.rs::TypedEnv` threading | `Environment.lean` |
| FNV-1a hash constants | `certified.rs::BridgeCertificate` hash table | `CertificateHash.lean` |

## What is NOT mechanized

The following are explicit gaps. The Rust code in these areas is
correlated to the Lean specification by inspection only.

| Gap | Rust location | Why not mechanized |
|---|---|---|
| Sampling vs exhaustive trace coverage | `proptest` integration | The Lean theorems quantify over all traces; proptest samples. A passing test is probabilistic, not absolute. |
| `TypedEnv` runtime type safety | `env.rs` (`Box<dyn Any + Send>`) | Lean uses an abstract `Env`; modeling Rust's `TypeId` would require embedding Rust's type system. |
| `Is<A,B>::cast` soundness | `witness.rs` (`unsafe fn cast`) | Lean has propositional equality natively; the Rust unsafe transmute is sound by construction but not machine-checked. |
| Proc macro expansion | `proptest-lockstep-derive/` | `CertifiedSynthesis.lean` verifies the algorithm; no theorem constrains the actual syn output. |
| GVar projection chain elaboration | `gvar.rs`, `op.rs` (lifetime/type plumbing) | `Projection.lean` covers the algebra; the Rust trait dispatch is unverified. |
| `dyn AnyAction` dispatch | `action.rs`, `runner.rs` | Lean uses an abstract `ActionIdx`; runtime trait-object dispatch is unverified. |
| Concurrent runtime (Shuttle/loom) | `concurrent.rs` | Lean models the recorded trace, not the scheduler that produces it. |
| Probabilistic effectiveness | `coverage.rs`, `shrinking.rs` heuristics | The bisimulation-guided shrinking algorithm has a Lean correctness condition; the heuristic for choosing what to shrink is unverified. |

## Field precedent

For comparison: most published artifacts with this kind of formalization
operate at the same level.

| Project | Approach | Implementation verified? |
|---|---|---|
| POPLmark (challenge benchmarks) | Mechanized metatheory of programming languages | No |
| Most ICFP artifact-track papers | Coq/Agda/Lean specs of the system in the paper | Usually no |
| `quickcheck-lockstep` (Haskell) | None | No |
| CompCert | C semantics + machine semantics + verified compiler | **Yes** (this is the gold standard) |
| seL4 | Microkernel verified against an abstract spec | **Yes** |
| RustBelt | Semantic model of Rust's type system in Coq/Iris | Verifies the soundness of `unsafe` patterns |
| Verus / Aeneas / Creusot | Frameworks for verifying actual Rust code | **Yes** (but tooling is research-grade) |

`proptest-lockstep` sits in the same tier as POPLmark and ICFP artifact
formalizations: a formalization of the metatheory plus an
implementation correlated to it by design.

## Closing the gap further

Three options that would tighten the trust boundary, ranked by
cost/value:

1. **(low cost, low value)** Property test: in
   `tests/correspondence.rs`, run a small `LockstepModel`, record the
   trace, and assert the Rust runner's behavior matches a hand-written
   transcription of `runner_passes`. Catches drift, not bugs.
2. **(moderate cost, moderate value)** Verus on
   `concurrent.rs::check_linearizability`. Verify the Rust function
   computes the same predicate as `Linearizability.lean::is_linearizable`.
   This is the highest-value single function to verify.
3. **(high cost, high value)** Aeneas extraction of a verifiable
   subset (the bridge algebra without `dyn`/`unsafe`). Useful for
   research pearl claims; expensive ongoing maintenance.

These are deliberately not on the roadmap. They are listed so reviewers
can see we considered them.
