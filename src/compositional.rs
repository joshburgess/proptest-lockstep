//! Compositional lockstep testing.
//!
//! Enables modular testing: verify subsystems independently, then
//! compose the guarantees. If subsystem A passes lockstep testing
//! and subsystem B passes lockstep testing, and their actions are
//! independent (don't interfere with each other), then their
//! composition also satisfies lockstep.
//!
//! This is based on compositional bisimulation from process algebra
//! (CCS, CSP), adapted for lockstep testing. The formal soundness
//! is proved in `Compositional.lean`.
//!
//! # Use Cases
//!
//! - **Layered architectures**: test database layer and network layer
//!   independently, compose the guarantees
//! - **Microservices**: test each service's state machine independently
//! - **Plugin systems**: test the core and each plugin separately
//!
//! # Architecture
//!
//! Two lockstep models are composed into a product model. The
//! product model's state is the pair of sub-states, and actions
//! are tagged to indicate which subsystem they target.

use std::fmt::Debug;


use crate::action::AnyAction;
use crate::env::TypedEnv;
use crate::model::LockstepModel;

// ---------------------------------------------------------------------------
// Composed model
// ---------------------------------------------------------------------------

/// A composed lockstep model from two independent subsystems.
///
/// Actions are tagged with `Left` or `Right` to indicate which
/// subsystem they target. The composed state is the product of
/// both sub-states.
///
/// Independence assumption: left actions don't affect right state
/// and vice versa. This is enforced by the type structure — each
/// interpreter only has access to its own sub-state.
#[derive(Debug, Clone)]
pub struct ComposedModel<L: LockstepModel, R: LockstepModel> {
    _phantom: std::marker::PhantomData<(L, R)>,
}

/// The composed model state: product of both sub-states.
#[derive(Debug, Clone, PartialEq)]
pub struct ComposedState<LS: Debug + Clone, RS: Debug + Clone> {
    pub left: LS,
    pub right: RS,
}

/// The composed SUT: product of both SUTs.
#[derive(Debug)]
pub struct ComposedSut<LS: Debug, RS: Debug> {
    pub left: LS,
    pub right: RS,
}

/// Tag indicating which subsystem an action targets.
#[derive(Debug, Clone)]
pub enum SubsystemAction {
    /// Action targets the left subsystem.
    Left(Box<dyn AnyAction>),
    /// Action targets the right subsystem.
    Right(Box<dyn AnyAction>),
}

impl std::fmt::Display for SubsystemAction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SubsystemAction::Left(a) => write!(f, "Left({:?})", a),
            SubsystemAction::Right(a) => write!(f, "Right({:?})", a),
        }
    }
}

// ---------------------------------------------------------------------------
// Runner for composed models
// ---------------------------------------------------------------------------

/// Run a composed lockstep test.
///
/// Generates actions for both subsystems, executes each against its
/// own sub-model and sub-SUT, and checks bridges independently.
/// The composition is sound because the subsystems are independent.
///
/// # Arguments
///
/// * `left_trace` — actions for the left subsystem
/// * `right_trace` — actions for the right subsystem
///
/// # Panics
///
/// If either subsystem's bridge check fails.
pub fn run_composed_test<L: LockstepModel, R: LockstepModel>(
    left_trace: &[Box<dyn AnyAction>],
    right_trace: &[Box<dyn AnyAction>],
) {
    // Test left subsystem
    let mut left_model = L::init_model();
    let mut left_sut = L::init_sut();
    let mut left_model_env = TypedEnv::new();
    let mut left_real_env = TypedEnv::new();
    let mut left_var_id = 0usize;

    for action in left_trace {
        let model_result = L::step_model(
            &mut left_model,
            action.as_ref(),
            &left_model_env,
        );
        let sut_result = L::step_sut(
            &mut left_sut,
            action.as_ref(),
            &left_real_env,
        );

        action.check_bridge(&*model_result, &*sut_result)
            .unwrap_or_else(|msg| {
                panic!(
                    "Lockstep mismatch in LEFT subsystem!\n  Action: {:?}\n{}",
                    action, msg
                )
            });

        action.store_model_var(left_var_id, &*model_result, &mut left_model_env);
        action.store_sut_var(left_var_id, &*sut_result, &mut left_real_env);
        left_var_id += 1;
    }

    // Test right subsystem
    let mut right_model = R::init_model();
    let mut right_sut = R::init_sut();
    let mut right_model_env = TypedEnv::new();
    let mut right_real_env = TypedEnv::new();
    let mut right_var_id = 0usize;

    for action in right_trace {
        let model_result = R::step_model(
            &mut right_model,
            action.as_ref(),
            &right_model_env,
        );
        let sut_result = R::step_sut(
            &mut right_sut,
            action.as_ref(),
            &right_real_env,
        );

        action.check_bridge(&*model_result, &*sut_result)
            .unwrap_or_else(|msg| {
                panic!(
                    "Lockstep mismatch in RIGHT subsystem!\n  Action: {:?}\n{}",
                    action, msg
                )
            });

        action.store_model_var(right_var_id, &*model_result, &mut right_model_env);
        action.store_sut_var(right_var_id, &*sut_result, &mut right_real_env);
        right_var_id += 1;
    }
}

/// Verify that two independently-tested subsystems can be composed.
///
/// This is a documentation function — the actual composition guarantee
/// comes from the `compositional_bisim` theorem in Lean, which proves
/// that independent bisimulations compose. This function just runs
/// both subsystem tests and confirms they pass.
pub fn verify_composition<L: LockstepModel, R: LockstepModel>(
    left_trace: &[Box<dyn AnyAction>],
    right_trace: &[Box<dyn AnyAction>],
) -> CompositionResult {
    let left_ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        run_composed_test::<L, R>(left_trace, &[]);
    })).is_ok();

    let right_ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        run_composed_test::<L, R>(&[], right_trace);
    })).is_ok();

    CompositionResult {
        left_passes: left_ok,
        right_passes: right_ok,
        composition_sound: left_ok && right_ok,
        left_steps: left_trace.len(),
        right_steps: right_trace.len(),
    }
}

/// Result of a compositional verification.
#[derive(Debug, Clone)]
pub struct CompositionResult {
    /// Whether the left subsystem passed.
    pub left_passes: bool,
    /// Whether the right subsystem passed.
    pub right_passes: bool,
    /// Whether the composition is sound (both pass).
    pub composition_sound: bool,
    /// Number of steps in the left trace.
    pub left_steps: usize,
    /// Number of steps in the right trace.
    pub right_steps: usize,
}

impl std::fmt::Display for CompositionResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Compositional verification: left={} ({} steps), right={} ({} steps), composed={}",
            if self.left_passes { "PASS" } else { "FAIL" },
            self.left_steps,
            if self.right_passes { "PASS" } else { "FAIL" },
            self.right_steps,
            if self.composition_sound { "SOUND" } else { "UNSOUND" },
        )
    }
}
