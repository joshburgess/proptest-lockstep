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
//! # Soundness (proved in `Soundness.lean`)
//!
//! - `lockstep_test_sound`: runner passing on all traces → `bounded_bisim`
//! - `deeper_test_stronger`: depth monotonicity for the test runner
//! - `testing_depth_increases_strength`: depth n+1 implies depth n
//! - `transparent_equiv_is_eq`: transparent bridge equivalence = equality
//! - `opaque_equiv_trivial`: opaque bridge equivalence is always true
//!
//! # Opacity and Behavioral Equivalence
//!
//! `Opaque<R, M>` weakens the guarantee from trace equivalence to
//! *behavioral equivalence*: a wrong handle is not detected at the
//! point of return, but IS detected later when the handle is *used*
//! and produces a different observable result. This is captured by
//! the bounded bisimulation: the opaque check passes at depth n, but
//! the behavioral difference manifests at depth n+k when the handle
//! is used in a subsequent action with a transparent bridge.
//!
//! # What Is NOT Formalized
//!
//! The Lean formalization covers the bridge algebra, the bisimulation
//! relation, and the runner correspondence. It does not formalize:
//! - The proptest generation/shrinking machinery
//! - The `TypedEnv` variable resolution mechanism
//! - Precondition filtering
//! - DPOR soundness (planned)
//! - The probabilistic guarantee (how many test cases are needed)
