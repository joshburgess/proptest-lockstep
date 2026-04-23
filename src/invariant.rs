//! State invariant checking for lockstep tests.
//!
//! Provides the [`InvariantModel`] trait -- a shared extension point
//! for lockstep models that maintain per-step state invariants.
//!
//! An invariant is a predicate on the model state that must hold at
//! every reachable state. If the invariant is violated, the test
//! fails immediately with a diagnostic message.
//!
//! This module is used by:
//! - [`crash_recovery`](crate::crash_recovery) -- invariant checked at
//!   every step and after crash recovery
//! - Future extensions (commutativity specs, eventual consistency,
//!   session consistency) will also build on this trait
//!
//! # Formalization
//!
//! The Lean formalization in `Invariant.lean` proves that if the
//! invariant holds initially and is preserved by every action, it
//! holds along all traces (`invariant_along_trace`).

use crate::model::LockstepModel;

/// Extension trait for lockstep models with per-step state invariants.
///
/// The invariant is checked at every step during test execution.
/// It should capture properties that hold at every reachable model
/// state, such as:
/// - "Balance is non-negative"
/// - "Tree is balanced"
/// - "Cache size ≤ capacity"
/// - "No duplicate keys"
///
/// The default implementation returns `true` (no invariant).
pub trait InvariantModel: LockstepModel {
    /// Check whether the model state satisfies the invariant.
    ///
    /// Called at every step during lockstep execution. If this
    /// returns `false`, the test panics with an invariant violation.
    fn invariant(_state: &Self::ModelState) -> bool {
        true
    }
}

/// Assert the invariant holds, panicking with a diagnostic message
/// if it doesn't. Used by extension runners (crash-recovery, etc.).
pub fn assert_invariant<M: InvariantModel>(state: &M::ModelState, context: &str) {
    assert!(
        M::invariant(state),
        "Invariant violation ({context})!\n  Model state: {state:?}",
    );
}
