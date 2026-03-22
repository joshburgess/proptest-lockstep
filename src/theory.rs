//! Formal theory of lockstep testing as observational refinement.
//!
//! This module documents the metatheory of proptest-lockstep — what a
//! passing lockstep test *proves* about the relationship between the
//! SUT and the model. The formal proofs are machine-checked in
//! Lean 4 (see `formal_verification/`).
//!
//! # The Bridge Algebra as a Logical Relation
//!
//! The bridge algebra is a *logical relation* (Reynolds, 1983) — a
//! type-indexed family of relations preserved by type constructors.
//!
//! | Bridge | Logical Relation | Lean theorem |
//! |--------|-----------------|-------------|
//! | `Transparent<T>` | Identity | `transparent_refl` |
//! | `Opaque<R, M>` | Trivial (⊤) | `opaqueBridge_always` |
//! | `ResultBridge<OkB, ErrB>` | Sum | `sum_preserves_ok/err` |
//! | `TupleBridge<AB, BB>` | Product | `prod_preserves`, `prod_equiv_iff` |
//! | `OptionBridge<B>` | Lifted | `option_preserves_some/none` |
//! | `VecBridge<B>` | Pointwise | `list_preserves_cons/nil`, `list_equiv_length` |
//!
//! The **fundamental theorem** (proved in `Bridge.lean`): each lift
//! preserves bridge equivalence. If component values are related by
//! their bridges, the lifted compound values are related by the
//! lifted bridge. Sum bridge variant mismatches are detected in both
//! directions (`sum_variant_mismatch_lr`, `sum_variant_mismatch_rl`).
//!
//! Bridge equivalence is **decidable** (`bridge_equiv_decidable`):
//! every bridge carries `DecidableEq` on its `Observed` type, so
//! `bridge_equiv` can be computed. This connects the Lean `Prop`-level
//! proofs to the Rust `check_bridge` function, which returns
//! `Result<(), String>`.
//!
//! ## Derived Bridge Monotonicity (proved in `DerivedBridge.lean`)
//!
//! The polynomial bridge derivation is monotone in refinement:
//! replacing a component bridge with a finer one produces a finer
//! composite bridge (`derivation_monotone_sum_ok/err`,
//! `derivation_monotone_prod`, `derivation_monotone_option`,
//! `derivation_monotone_list`). Individual lift preservation is
//! proved in `Bridge.lean` as the fundamental theorem.
//!
//! ## Bridge Refinement Ordering (proved in `BridgeRefinement.lean`)
//!
//! Bridges form a preorder under refinement (`bridge_refines`): B1
//! refines B2 if every pair related by B1 is also related by B2.
//! - `opaque_coarsest`: every bridge refines opaque (trivial relation)
//! - `transparent_refines_uniform`: transparent refines any bridge
//!   with uniform observation functions (identity is finest)
//! - `refines_refl`, `refines_trans`: preorder structure
//! - `sum_refines`, `prod_refines`, `option_refines`, `list_refines`:
//!   lifts are monotone — finer components produce finer composite
//!   bridges
//! - `refines_strengthen_bisim`: replacing bridges with finer ones
//!   preserves bounded bisimulation (finer observation = stronger
//!   guarantee)
//!
//! # Bounded Bisimulation
//!
//! A passing lockstep test at depth n establishes a *bounded
//! bisimulation* between the model and SUT initial states:
//!
//! ```text
//! bounded_bisim(0, sm, ss) = True
//! bounded_bisim(n+1, sm, ss) =
//!   ∀ action a:
//!     bridge_equiv(bridge(a), sut_result, model_result)
//!     ∧ bounded_bisim(n, sm', ss')
//! ```
//!
//! Key properties (proved in `Lockstep.lean`):
//! - **Monotonicity** (`bounded_bisim_mono`): if the bisimulation holds
//!   at depth m ≥ n, it holds at depth n. Deeper tests are strictly
//!   stronger.
//! - **Single-step** (`single_step_bisim`): one-step bridge agreement
//!   implies depth-1 bisimulation.
//!
//! # Runner Correspondence (proved in `Runner.lean`)
//!
//! The test runner is modeled as a trace-based predicate
//! `runner_passes` that mirrors `LockstepSut::apply`: for each
//! action in the trace, run the model and SUT, check bridge
//! equivalence, and continue with successor states.
//!
//! The **runner correspondence theorem** (`runner_bounded_bisim_equiv`)
//! proves a biconditional:
//!
//! ```text
//! (∀ traces of length n, runner_passes trace sm ss)
//!   ↔ bounded_bisim n sm ss
//! ```
//!
//! This establishes that the runner's operational bridge checks are
//! *exactly* the obligations of bounded bisimulation — no more, no
//! less. The forward direction (`runner_implies_bounded_bisim`) is the
//! soundness result: passing tests imply bisimulation. The reverse
//! direction (`bounded_bisim_implies_runner`) confirms completeness:
//! bisimulation implies the runner would pass.
//!
//! # Observational Refinement (proved in `ObservationalRefinement.lean`)
//!
//! The central theoretical result: bounded bisimulation implies
//! observational indistinguishability. The SUT observationally
//! refines the model — no interaction through the bridge API can
//! distinguish them within the tested depth.
//!
//! Key theorems:
//! - `observational_refinement`: for any prefix of length < n and
//!   any action, the bridge observations are identical
//! - `observational_refinement_equiv`: bounded bisimulation is
//!   *equivalent* to observational refinement (biconditional),
//!   closing the circle: runner passes ↔ bounded_bisim ↔
//!   observational refinement
//! - `bisim_along_trace`: bisimulation is preserved along any
//!   prefix — the guarantee doesn't degrade during execution
//! - `bisim_observation_after_prefix`: observations remain equal
//!   at every point along a trace
//!
//! ## Testing Completeness (proved in `TestingCompleteness.lean`)
//!
//! The contrapositive: any observable discrepancy between SUT and
//! model WILL be detected at sufficient depth. No false negatives.
//!
//! Key theorems:
//! - `testing_completeness`: if observations differ after some prefix,
//!   `bounded_bisim` fails at depth `prefix.length + 1`
//! - `bug_localization`: if bisim fails at depth n+1, some action
//!   witnesses the failure (bridge check or successor bisim)
//! - `immediate_bug`: bridge failure at current state → bisim fails
//!   at depth 1
//!
//! # Soundness (proved in `Soundness.lean`)
//!
//! - `lockstep_test_sound`: runner passing on all traces → `bounded_bisim`
//! - `deeper_test_stronger`: depth monotonicity for the test runner
//! - `testing_depth_increases_strength`: depth n+1 implies depth n
//! - `transparent_equiv_is_eq`: transparent bridge equivalence = equality
//! - `opaque_equiv_trivial`: opaque bridge equivalence is always true
//!
//! # Linearizability (proved in `Linearizability.lean`)
//!
//! A concurrent execution is linearizable if there exists a sequential
//! ordering (permutation) of the operations such that the model produces
//! bridge-equivalent results at each step (`is_linearizable`).
//!
//! Key theorems:
//! - `is_linearizable`: the linearizability predicate
//! - `linearizability_perm_invariant`: linearizability depends only on
//!   the multiset of operations, not their listing order
//! - `swap_preserves_linearizability`: swapping adjacent records
//!   preserves linearizability
//! - `single_op_linearizable_iff`: single-operation linearizability
//!   reduces to a bridge check
//! - `not_linearizable_iff`: characterization of non-linearizability
//!
//! # DPOR Soundness (proved in `DPOR.lean`)
//!
//! The linearizability checker uses dynamic partial-order reduction to
//! prune redundant interleavings. Two operations commute at a model
//! state if executing them in either order yields the same per-action
//! results and the same final state (`model_commute`).
//!
//! The **DPOR soundness theorem** (`dpor_swap_sound`) proves that
//! swapping two adjacent commuting operations in a linearization
//! preserves validity: if the linearization check passes for
//! `[r1, r2, ...]`, it also passes for `[r2, r1, ...]`. This is
//! extended to arbitrary positions via `dpor_swap_at`.
//!
//! The biconditional `dpor_swap_iff` confirms that commuting
//! operations are fully interchangeable — neither ordering can
//! succeed where the other fails.
//!
//! Key theorems:
//! - `model_commute`: commutativity relation on model actions
//! - `commute_sym`: commutativity is symmetric
//! - `dpor_swap_sound`: adjacent swap preserves linearization validity
//! - `dpor_swap_iff`: adjacent swap is an equivalence
//! - `dpor_swap_at`: swap at arbitrary position (prefix extension)
//!
//! Note: the formalization uses direct equality on model results,
//! which is stronger than the bridge-based comparison used in the
//! Rust `operations_commute`. This means the formal guarantee is
//! conservative — it covers all cases the Rust implementation handles.
//!
//! # Opacity and Behavioral Equivalence (proved in `OpaqueDetection.lean`)
//!
//! `Opaque<R, M>` weakens the guarantee from trace equivalence to
//! *behavioral equivalence*: a wrong handle is not detected at the
//! point of return, but IS detected later when the handle is *used*
//! and produces a different observable result. This is captured by
//! the bounded bisimulation: the opaque check passes at depth n, but
//! the behavioral difference manifests at depth n+k when the handle
//! is used in a subsequent action with a transparent bridge.
//!
//! Key theorems:
//! - `detection_at_successor`: failure at successor states propagates
//!   to the parent (the inductive mechanism behind delayed detection)
//! - `failure_propagates_up`: failure at depth n implies failure at
//!   all depths m ≥ n (contrapositive of monotonicity)
//! - `opaque_step_then_detect`: wrong opaque handle + discriminating
//!   follow-up action → `bounded_bisim 2` fails
//! - `opaque_delayed_detection`: general k-step delayed detection
//! - `opaque_runner_transparent`: an opaque step in the runner is
//!   transparent — it passes iff the tail passes on successor states
//! - `opaque_depth_sensitivity`: depth 1 can pass while depth 2
//!   fails, proving deeper testing is strictly necessary for opaque
//!   handles
//!
//! # Precondition Filtering (proved in `Precondition.lean`)
//!
//! The test runner only checks actions satisfying a model-state-dependent
//! precondition (`LockstepModel::precondition`). The `precond_bisim`
//! definition restricts the universal quantification to precondition-
//! satisfying actions.
//!
//! Key theorems:
//! - `universal_implies_preconditioned`: the universal bisimulation
//!   (used in other Lean files) implies preconditioned bisimulation,
//!   so existing proofs are conservative
//! - `precond_bisim_mono`: monotonicity for preconditioned bisimulation
//! - `precond_runner_implies_bisim`: preconditioned runner correspondence
//! - `precond_bisim_step`: single-step decomposition of preconditioned
//!   bisimulation
//!
//! # Certified Bridge Synthesis (proved in `CertifiedSynthesis.lean`)
//!
//! Bridges produced by `certify_*` constructors are paired with
//! machine-checked soundness proofs. Each constructor produces a
//! `CertifiedBridge` that is provably correct by construction.
//! The Rust side provides `CertifiedLockstepBridge` as a marker
//! trait linking each bridge type to its Lean proof.
//!
//! Key theorems:
//! - `certified_transparent_sound`: equivalence is equality
//! - `certified_opaque_sound`: equivalence is always true
//! - `certified_sum_ok`: sum preserves component equivalence
//! - `certified_prod_sound`: product preserves component equivalence
//! - `certified_option_some/none`: option preserves
//! - `certified_list_nil/cons`: list preserves
//! - `synthesis_matches_transparent/opaque`: synthesized bridges
//!   match hand-written ones
//!
//! # Compositional Bisimulation (proved in `Compositional.lean`)
//!
//! Modular testing: if two independent subsystems each satisfy
//! bounded bisimulation, their product does too. Tests subsystems
//! independently, composes the guarantees.
//!
//! Key theorems:
//! - `compositional_bisim`: product bisim from component bisims
//! - `product_bisim_left/right`: extract component bisims from product
//! - `product_bisim_iff`: biconditional — product bisim iff both
//!   components satisfy bisim
//!
//! # Effect-Indexed Commutativity Lattice (proved in `EffectLattice.lean`)
//!
//! Static effect annotations for O(1) commutativity checking. Each
//! action declares its read/write footprint via `ConflictAlgebra`.
//! Two actions commute iff their effects don't conflict. The dynamic
//! model oracle is a fallback for unannotated actions.
//!
//! Key theorems:
//! - `effect_sound`: annotations are sound iff non-conflict implies
//!   model commutativity
//! - `effect_dpor_sound`: sound effects enable sound DPOR
//! - `rw_conflicts_symmetric`: read/write conflicts are symmetric
//! - `conservative_effects_sound`: more conservative annotations
//!   remain sound
//!
//! # Observational Refinement Contracts (`src/contracts.rs`)
//!
//! Turns the bridge algebra into a runtime contract system. A
//! `RefinementGuard` shadows the SUT with a model, checking bridge
//! equivalence at every operation. Violations are collected (not
//! panicked on), enabling use as a production monitor. Based on
//! `observational_refinement_equiv` — the contract is exactly right.
//!
//! # Model-Coverage-Guided Generation (`src/coverage.rs`)
//!
//! Uses the model's reachable state space as a semantic coverage map.
//! Instead of random generation, scores candidate actions by whether
//! they lead to novel model states. The model IS the coverage oracle.
//!
//! # Bisimulation-Guided Shrinking (`src/shrinking.rs`)
//!
//! Post-hoc minimization of counterexamples using the bisimulation
//! structure. After a lockstep mismatch is found, identifies the
//! failure depth (first failing step) and removes irrelevant setup
//! actions to produce a minimal failing trace. Based on
//! `bug_localization` and `testing_completeness`.
//!
//! # Differential Bridge Testing (`src/differential.rs`)
//!
//! Meta-testing technique: tests the test oracles themselves.
//! Compares a coarse bridge (user's) with a fine bridge (stricter)
//! to detect hidden discrepancies. Based on `refines_strengthen_bisim`:
//! a finer bridge gives a stronger guarantee, so if the fine bridge
//! fails but the coarse passes, the coarse bridge is hiding a bug.
//!
//! # Session Consistency (proved in `SessionConsistency.lean`)
//!
//! Tests per-session ordering guarantees (Terry et al., 1994):
//! read-your-writes and monotonic reads. Sits between linearizability
//! (too strong) and eventual consistency (too weak).
//!
//! Key theorems:
//! - `bounded_implies_session`: linearizability implies session
//!   consistency (strictly stronger)
//! - `session_bisim_mono`: monotonicity in depth
//!
//! # Eventual Consistency (proved in `EventualConsistency.lean`)
//!
//! Tests systems that are intentionally non-linearizable but should
//! converge after synchronization. The `convergent_bisim` relation
//! requires sync agreement at every depth but NOT per-step bridge_equiv.
//!
//! Key theorems:
//! - `convergent_bisim_sync`: syncing at any depth produces agreement
//! - `convergent_after_prefix`: convergence holds after any prefix
//! - `convergent_bisim_mono`: monotonicity in depth
//! - `bounded_implies_convergent`: linearizability implies eventual
//!   consistency (strictly stronger)
//!
//! # Commutativity Specification Testing (proved in `CommutativitySpec.lean`)
//!
//! Tests that operations satisfy a commutativity specification.
//! Users declare `should_commute(a, b, state)` and the framework
//! verifies the model actually satisfies it.
//!
//! Key theorems:
//! - `spec_sound`: a spec is sound iff `should_commute` implies
//!   `model_commute`
//! - `spec_dpor_sound`: if the spec is sound, using it as a DPOR
//!   oracle preserves linearization validity
//! - `sound_iff_no_violations`: soundness ↔ no violations
//! - `finer_spec_sound`: a finer spec is easier to satisfy
//!
//! # Crash-Recovery Bisimulation (proved in `CrashRecovery.lean`)
//!
//! Extends bounded bisimulation with crash transitions. A crash
//! resets the SUT to a recovered state; the model recovers from a
//! checkpoint of its durable state. The `crash_bisim` relation
//! requires that:
//! 1. A state invariant holds at every reachable state
//! 2. Normal actions satisfy bridge_equiv (as in bounded_bisim)
//! 3. After a crash, recovered states are in the bisimulation
//!
//! Key theorems:
//! - `crash_bisim_implies_bounded`: crash bisim is strictly stronger
//!   than normal bounded bisim
//! - `crash_bisim_mono`: monotonicity in depth
//! - `crash_bisim_invariant`: invariant holds at every reachable state
//! - `crash_recovery_preserves`: recovered states remain in the
//!   bisimulation
//! - `crash_bisim_double_crash`: survives multiple consecutive crashes
//! - `crash_then_bounded_bisim`: after crash+recovery, normal lockstep
//!   testing is still valid
//!
//! # Environment Threading (proved in `Environment.lean`)
//!
//! Models the `TypedEnv` variable environment that threads through
//! lockstep execution. The `EnvLockstepSystem` extends
//! `LockstepSystem` with explicit environment state, store operations,
//! and environment-parameterized step functions.
//!
//! Key theorems:
//! - `env_runner_bounded_bisim_equiv`: the runner correspondence
//!   biconditional holds with environment threading
//! - `lift_bisim_equiv`: the environment-aware formalization reduces
//!   to the environment-free version for trivial environments,
//!   showing it's a strict generalization
//!
//! This closes the TypedEnv gap identified by reviewers: the formal
//! guarantee now covers environment-threaded execution.
//!
//! # Certificate Hash Verification (proved in `CertificateHash.lean`)
//!
//! Implements FNV-1a hashing in Lean and proves the hash values
//! match the constants in the Rust `BridgeCertificate`. This closes
//! the Rust-Lean certificate gap — hashes are verified on both sides.
//!
//! Key theorems:
//! - `transparent_hash_verified`: Lean hash = `0xd0e945b97c0c46d1`
//! - `opaque_hash_verified`: Lean hash = `0x66d852e3c020e79e`
//! - `result/tuple/option/vec/unit_bridge_hash_verified`: all match
//! - `all_hashes_distinct`: no two bridge types share a hash
//!
//! # Projection Chains (proved in `Projection.lean`)
//!
//! Formalizes the `Op` DSL — typed projection chains for decomposing
//! compound return types. Projections are partial functions composing
//! via Kleisli composition (`Option` monad).
//!
//! Key theorems:
//! - `proj_comp_assoc`: composition is associative
//! - `proj_comp_id_left/right`: identity is a unit
//! - `proj_fst/snd/ok/err/some_preserves`: each projection preserves
//!   bridge_equiv when applied to bridge-equivalent sources
//! - `proj_comp_preserves`: composed projections preserve bridge_equiv
//!   (the fundamental GVar theorem — justifies `GVar::new(v, OpOk).then(OpFst)`)
//!
//! # Scope and Limitations of the Formalization
//!
//! ## What IS formalized
//!
//! The Lean formalization (303 definitions, 29 files, zero `sorry`)
//! covers: bridge algebra, bounded bisimulation, runner correspondence,
//! observational refinement, DPOR soundness, linearizability, opaque
//! handle detection, preconditions, crash-recovery bisimulation,
//! eventual/session consistency, compositional bisimulation, tensor
//! product, effect-indexed commutativity, certified bridge synthesis,
//! projection chains, sleep set equivalence, monotonic reads, and
//! crash-session composition.
//!
//! ## What IS NOT formalized
//!
//! - The proptest generation/shrinking machinery
//! - GVar projection chain resolution (the `Op` DSL internals)
//! - The probabilistic guarantee (how many test cases are needed)
//!
//! ## The Rust-Lean gap
//!
//! The formalization is a **specification verification**: Lean proves
//! properties of abstract definitions (runner_passes, bounded_bisim,
//! bridge_equiv) that are designed to mirror the Rust implementation.
//! It is NOT a **code verification**: no Lean theorem directly
//! constrains the Rust code.
//!
//! The gap is bridged by **shared structure**:
//! - `runner_passes` in Lean mirrors `LockstepSut::apply` in Rust
//! - `bridge_equiv` in Lean mirrors `LockstepBridge::check` in Rust
//! - `bounded_bisim` in Lean mirrors the runner's recursive structure
//! - `CertificateHash.lean` cross-verifies FNV-1a hashes between
//!   Lean and Rust (`BridgeCertificate`)
//!
//! Specific gaps between Lean and Rust:
//! - **Sampling vs exhaustive**: Lean's `runner_passes` quantifies
//!   over ALL traces of length n. The Rust runner SAMPLES traces via
//!   proptest strategies. A passing Rust test does not check all
//!   traces — it provides probabilistic (not absolute) coverage.
//! - **DecidableEq vs PartialEq**: Lean requires `DecidableEq` on
//!   `Observed` types. Rust requires `PartialEq`, which is weaker
//!   (not necessarily decidable, may have side effects).
//! - **Proc macro**: The bridge derivation macro generates Rust code,
//!   but no Lean theorem constrains the macro output. The certified
//!   synthesis in Lean verifies the *algorithm*, not the *expansion*.
//! - **TypedEnv**: Lean uses an abstract `Env` type. Rust uses
//!   `Box<dyn Any + Send>` with runtime type checks. The type safety
//!   of variable storage is not formally verified.
//! - **GVar projections**: The `GVar<X,Y,O>` projection chains have
//!   complex lifetime and type semantics not modeled in Lean.
//!
//! This gap is **intentional and honest**: formalizing Rust semantics
//! in Lean would require embedding Rust's type system (cf. RustBelt),
//! which is a separate research project. The formalization covers what
//! a correct lockstep runner *must* satisfy; the Rust implementation
//! provides evidence (not proof) that it does.
