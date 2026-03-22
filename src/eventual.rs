//! Eventual consistency testing.
//!
//! Tests systems that are intentionally non-linearizable but should
//! converge: after all operations complete (quiescence), every
//! replica or view agrees on the final state.
//!
//! This is weaker than linearizability — individual operations may
//! return stale results — but stronger than no guarantee at all.
//! The framework checks convergence by running operations through
//! the model and SUT, allowing per-step mismatches, but requiring
//! that a final "sync" operation produces matching observations.
//!
//! This is the first formally verified eventual consistency
//! property-based testing framework. The soundness is proved in
//! `EventualConsistency.lean`.
//!
//! # Use Cases
//!
//! - **CRDTs**: convergent replicated data types
//! - **Eventually-consistent caches**: `evmap`, `left-right`
//! - **Gossip protocols**: state that propagates lazily
//! - **Read replicas**: reads may be stale until sync
//!
//! # Architecture
//!
//! Users implement [`EventualConsistencyModel`] on top of
//! [`InvariantModel`](crate::invariant::InvariantModel):
//! - `sync` — force the SUT to a consistent state (flush, merge, etc.)
//! - `model_sync` — the model's equivalent sync operation
//! - `convergence_check` — compare model and SUT after sync

use std::fmt::Debug;

use proptest_state_machine::ReferenceStateMachine;

use crate::action::AnyAction;
use crate::env::TypedEnv;
use crate::invariant::{assert_invariant, InvariantModel};
use crate::runner::LockstepRef;

// ---------------------------------------------------------------------------
// Trait
// ---------------------------------------------------------------------------

/// Extension trait for lockstep models with eventual consistency.
///
/// Unlike standard lockstep testing (which checks bridge_equiv at
/// every step), eventual consistency allows per-step mismatches.
/// The only requirement is that after a `sync` operation, the model
/// and SUT agree on the observable state.
pub trait EventualConsistencyModel: InvariantModel {
    /// The observable state after synchronization.
    ///
    /// This is what must match between model and SUT after sync.
    /// For a CRDT, this might be the merged value.
    /// For a cache, this might be the full contents.
    type ObservableState: Debug + PartialEq + Clone + 'static;

    /// Force the SUT to a consistent state.
    ///
    /// For a cache: flush pending writes and refresh stale reads.
    /// For a CRDT: merge all replicas.
    /// For a read replica: sync with the primary.
    fn sut_sync(sut: &mut Self::Sut) -> Self::ObservableState;

    /// Get the model's observable state after sync.
    ///
    /// The model is always "synced" (it's the source of truth),
    /// so this just extracts the observable state.
    fn model_sync(state: &Self::ModelState) -> Self::ObservableState;
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for eventual consistency tests.
#[derive(Debug, Clone)]
pub struct EventualConsistencyConfig {
    /// Number of proptest cases to generate.
    pub cases: u32,

    /// Sequence length range.
    pub min_ops: usize,
    pub max_ops: usize,

    /// Number of sync points per test run.
    /// Sync is checked at the end, and optionally at intermediate points.
    pub intermediate_syncs: usize,
}

impl Default for EventualConsistencyConfig {
    fn default() -> Self {
        EventualConsistencyConfig {
            cases: 100,
            min_ops: 5,
            max_ops: 30,
            intermediate_syncs: 2,
        }
    }
}

// ---------------------------------------------------------------------------
// Runner
// ---------------------------------------------------------------------------

/// Run an eventual consistency test.
///
/// Generates random action sequences, executes them against both
/// model and SUT WITHOUT checking bridge_equiv at each step (allowing
/// stale reads). At sync points and at the end, verifies that
/// `sut_sync()` and `model_sync()` produce the same observable state.
///
/// # Panics
///
/// - If the observable states diverge after sync (convergence failure)
/// - If the invariant is violated at any step
pub fn run_eventual_consistency_test<M: EventualConsistencyModel>(
    config: EventualConsistencyConfig,
) {
    let proptest_config = proptest::test_runner::Config {
        cases: config.cases,
        ..Default::default()
    };

    let size = config.min_ops..config.max_ops;

    proptest::proptest!(proptest_config, |((_initial_state, transitions, _seen_counter) in
        <LockstepRef<M> as ReferenceStateMachine>::sequential_strategy(size))| {

        let mut model_state = M::init_model();
        let mut sut = M::init_sut();
        let mut model_env = TypedEnv::new();
        let mut real_env = TypedEnv::new();
        let mut next_var_id: usize = 0;

        // Calculate sync points (evenly spaced through the sequence)
        let total = transitions.len();
        let sync_interval = if config.intermediate_syncs > 0 && total > 0 {
            total / (config.intermediate_syncs + 1)
        } else {
            usize::MAX
        };

        for (step, transition) in transitions.iter().enumerate() {
            assert_invariant::<M>(&model_state, "before step");

            // Run model
            let model_result = M::step_model(
                &mut model_state,
                transition.as_ref(),
                &model_env,
            );

            // Run SUT — no bridge check! (eventual consistency allows mismatches)
            let sut_result = M::step_sut(
                &mut sut,
                transition.as_ref(),
                &real_env,
            );

            // Store variables (both sides)
            let var_id = next_var_id;
            transition.store_model_var(var_id, &*model_result, &mut model_env);
            transition.store_sut_var(var_id, &*sut_result, &mut real_env);
            next_var_id += 1;

            // Intermediate sync check
            if sync_interval < usize::MAX && step > 0 && step % sync_interval == 0 {
                let sut_obs = M::sut_sync(&mut sut);
                let model_obs = M::model_sync(&model_state);
                assert_eq!(
                    sut_obs, model_obs,
                    "Convergence failure at intermediate sync (step {step})!\n\
                     SUT observable:   {sut_obs:?}\n\
                     Model observable: {model_obs:?}"
                );
            }
        }

        // Final sync: this MUST converge
        assert_invariant::<M>(&model_state, "before final sync");
        let sut_obs = M::sut_sync(&mut sut);
        let model_obs = M::model_sync(&model_state);
        assert_eq!(
            sut_obs, model_obs,
            "Convergence failure at final sync!\n\
             SUT observable:   {sut_obs:?}\n\
             Model observable: {model_obs:?}"
        );
    });
}
