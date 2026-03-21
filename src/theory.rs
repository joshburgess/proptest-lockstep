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
//! lifted bridge.
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
//! # Soundness (proved in `Soundness.lean`)
//!
//! - `transparent_equiv_is_eq`: transparent bridge equivalence = equality
//! - `opaque_equiv_trivial`: opaque bridge equivalence is always true
//! - `sum_bridge_sound_ok/err`: sum bridge correctly classifies variants
//! - `sum_bridge_variant_mismatch_lr/rl`: sum bridge detects variant mismatches
//! - `prod_bridge_sound`: product equivalence ↔ component equivalence
//! - `deeper_test_stronger`: depth monotonicity for the test runner
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
//! The Lean formalization covers the algebraic properties of the
//! bridge algebra and the bisimulation relation. It does not
//! formalize:
//! - The proptest generation/shrinking machinery
//! - The `TypedEnv` variable resolution mechanism
//! - Precondition filtering
//! - DPOR soundness (planned)
//! - The probabilistic guarantee (how many test cases are needed)
//!
//! The connection between the test runner's operational behavior and
//! the bisimulation is stated informally: the runner checks exactly
//! the conditions of `bounded_bisim` at each step.
