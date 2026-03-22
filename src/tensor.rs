//! Tensor product composition (shared-state).
//!
//! Extends compositional testing from independent subsystems
//! (product composition) to subsystems that share state (tensor
//! product composition). Two subsystems can read/write a common
//! shared resource, and the framework verifies that their combined
//! behavior is correct.
//!
//! The product composition (`compositional.rs`) requires independence:
//! actions from sys1 don't affect sys2's state. The tensor product
//! relaxes this: subsystems share a common state component, and
//! actions from either subsystem can modify it.
//!
//! # Architecture
//!
//! A tensor product system has:
//! - Per-subsystem local state (independent)
//! - Shared state (accessed by both subsystems)
//! - Actions tagged with which subsystem they belong to
//!
//! The framework verifies that the shared state is accessed
//! consistently — both subsystems' models agree on the shared
//! state after any interleaving of actions.

use std::any::Any;
use std::fmt::Debug;

use crate::action::AnyAction;

/// A system with shared state between two subsystems.
///
/// Each subsystem has its own local state, plus a shared state
/// component that both can read and modify.
#[derive(Debug, Clone, PartialEq)]
pub struct SharedState<L: Debug + Clone, R: Debug + Clone, S: Debug + Clone> {
    /// Left subsystem's local state.
    pub left: L,
    /// Right subsystem's local state.
    pub right: R,
    /// State shared between both subsystems.
    pub shared: S,
}

/// Result of a tensor product test.
#[derive(Debug, Clone)]
pub struct TensorResult {
    /// Whether the test passed (shared state is consistent).
    pub passed: bool,
    /// Number of steps executed.
    pub steps: usize,
    /// Number of shared state accesses.
    pub shared_accesses: usize,
}

impl std::fmt::Display for TensorResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Tensor product: {} ({} steps, {} shared accesses)",
            if self.passed { "PASS" } else { "FAIL" },
            self.steps,
            self.shared_accesses,
        )
    }
}

/// Run a tensor product test with interleaved actions.
///
/// Takes two sequences of actions (one per subsystem) and interleaves
/// them. Both operate on a shared model/SUT state. After each action,
/// checks that the shared state is consistent between model and SUT.
///
/// # Arguments
///
/// * `left_actions` — actions for the left subsystem
/// * `right_actions` — actions for the right subsystem
/// * `init_model` — initial shared model state
/// * `init_sut` — initial shared SUT state
/// * `step_model` — execute an action on the model
/// * `step_sut` — execute an action on the SUT
/// * `check` — compare model and SUT after each step
pub fn run_tensor_test<S: Debug + Clone + PartialEq>(
    left_actions: &[Box<dyn AnyAction>],
    right_actions: &[Box<dyn AnyAction>],
    init_model: S,
    init_sut: S,
    step_model: impl Fn(&mut S, &dyn AnyAction) -> Box<dyn Any>,
    step_sut: impl Fn(&mut S, &dyn AnyAction) -> Box<dyn Any>,
    check: impl Fn(&dyn Any, &dyn Any, &dyn AnyAction) -> Result<(), String>,
) -> TensorResult {
    let mut model = init_model;
    let mut sut = init_sut;
    let mut steps = 0;
    let mut shared_accesses = 0;
    let mut li = 0;
    let mut ri = 0;

    // Interleave: alternate left and right actions
    while li < left_actions.len() || ri < right_actions.len() {
        // Pick the next action (alternate, favoring whichever has more remaining)
        let action: &dyn AnyAction = if li < left_actions.len()
            && (ri >= right_actions.len() || li <= ri)
        {
            let a = left_actions[li].as_ref();
            li += 1;
            a
        } else {
            let a = right_actions[ri].as_ref();
            ri += 1;
            a
        };

        let model_result = step_model(&mut model, action);
        let sut_result = step_sut(&mut sut, action);

        if let Err(msg) = check(&*model_result, &*sut_result, action) {
            panic!(
                "Tensor product mismatch at step {}!\n  Action: {:?}\n{}",
                steps, action, msg,
            );
        }

        steps += 1;
        shared_accesses += 1;
    }

    // Final consistency check: shared states should be equal
    assert_eq!(
        model, sut,
        "Tensor product: final shared states differ"
    );

    TensorResult {
        passed: true,
        steps,
        shared_accesses,
    }
}
