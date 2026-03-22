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
//! # What Is NOT Formalized
//!
//! The Lean formalization covers the bridge algebra, the bisimulation
//! relation, the runner correspondence, DPOR soundness, opaque handle
//! detection, and precondition filtering. It does not formalize:
//! - The proptest generation/shrinking machinery
//! - The `TypedEnv` variable resolution mechanism
//! - The probabilistic guarantee (how many test cases are needed)
