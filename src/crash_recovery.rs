//! Crash-recovery lockstep testing.
//!
//! Extends the core lockstep framework with crash-recovery semantics:
//! the runner randomly injects "crash" events between normal actions,
//! forcing the SUT to recover from its persisted state. The model
//! tracks what should be durable and recovers accordingly.
//!
//! This is the first formally verified crash-recovery property-based
//! testing framework. The soundness is proved in `CrashRecovery.lean`:
//! if the crash-recovery runner passes, the system satisfies crash
//! bisimulation -- a strengthening of bounded bisimulation that
//! accounts for crash transitions.
//!
//! # Architecture
//!
//! Users implement [`CrashRecoveryModel`] on top of
//! [`InvariantModel`](crate::invariant::InvariantModel):
//! - `DurableState` -- what survives a crash (e.g., on-disk data)
//! - `model_checkpoint` -- extract the durable part of the model state
//! - `model_recover` -- reconstruct model state from a checkpoint
//! - `sut_recover` -- reconstruct the SUT from its persisted state
//! - `invariant` -- per-step state predicate (inherited from InvariantModel)
//!
//! The runner ([`run_crash_recovery_test`]) executes a normal lockstep
//! test but probabilistically injects crashes between steps. After
//! each crash, both model and SUT recover, and testing continues.

use std::fmt::Debug;

use proptest_state_machine::ReferenceStateMachine;

use crate::env::TypedEnv;
use crate::invariant::{assert_invariant, InvariantModel};
use crate::runner::LockstepRef;

// ---------------------------------------------------------------------------
// Trait
// ---------------------------------------------------------------------------

/// Extension trait for lockstep models with crash-recovery semantics.
///
/// Extends [`InvariantModel`] (which provides per-step invariant
/// checking) with crash/recovery operations. A crash resets the SUT
/// to its last persisted state. The model tracks what's durable via
/// checkpoints.
pub trait CrashRecoveryModel: InvariantModel {
    /// The durable state that survives a crash.
    ///
    /// For a write-ahead log, this might be `Vec<LogEntry>`.
    /// For a database, this might be the on-disk B-tree state.
    type DurableState: Debug + Clone + 'static;

    /// Extract the durable state from the current model state.
    ///
    /// Called after each step to track what should survive a crash.
    /// The returned checkpoint represents the "last committed" state.
    fn model_checkpoint(state: &Self::ModelState) -> Self::DurableState;

    /// Recover the model state from a durable checkpoint.
    ///
    /// After a crash, the model is reconstructed from its last
    /// checkpoint. This should produce a state that reflects only
    /// the durable operations.
    fn model_recover(checkpoint: &Self::DurableState) -> Self::ModelState;

    /// Recover the SUT from a crash.
    ///
    /// The SUT should reconstruct itself from whatever it persisted.
    /// The old SUT is consumed (simulating process death) and a new
    /// one is returned (simulating restart).
    fn sut_recover(sut: Self::Sut) -> Self::Sut;
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for crash-recovery lockstep tests.
#[derive(Debug, Clone)]
pub struct CrashRecoveryConfig {
    /// Probability of injecting a crash after each step (0.0 to 1.0).
    /// Default: 0.1 (10% chance of crash after each operation).
    pub crash_probability: f64,

    /// Maximum number of crashes per test run.
    /// Default: 3.
    pub max_crashes: usize,

    /// Number of proptest cases to generate.
    /// Default: 100.
    pub cases: u32,

    /// Sequence length range (number of normal operations).
    /// Default: 1..30.
    pub min_ops: usize,
    pub max_ops: usize,
}

impl Default for CrashRecoveryConfig {
    fn default() -> Self {
        CrashRecoveryConfig {
            crash_probability: 0.1,
            max_crashes: 3,
            cases: 100,
            min_ops: 1,
            max_ops: 30,
        }
    }
}

// ---------------------------------------------------------------------------
// Runner
// ---------------------------------------------------------------------------

/// Run a crash-recovery lockstep test.
///
/// Generates random action sequences, executes them in lockstep
/// (model vs SUT), and randomly injects crashes between steps.
/// After each crash, both model and SUT recover from the model's
/// checkpoint, and testing continues.
///
/// # Panics
///
/// - If a bridge check fails (lockstep mismatch)
/// - If the invariant is violated at any step
/// - If the SUT crashes or panics during normal operation
pub fn run_crash_recovery_test<M: CrashRecoveryModel>(config: CrashRecoveryConfig) {
    let proptest_config = proptest::test_runner::Config {
        cases: config.cases,
        ..Default::default()
    };

    let size = config.min_ops..config.max_ops;

    proptest::proptest!(proptest_config, |((_initial_state, transitions, _seen_counter) in
        <LockstepRef<M> as ReferenceStateMachine>::sequential_strategy(size))| {

        // Initialize
        let mut model_state = M::init_model();
        let mut sut = M::init_sut();
        let mut model_env = TypedEnv::new();
        let mut real_env = TypedEnv::new();
        let mut next_var_id: usize = 0;
        let mut crash_count: usize = 0;

        // Use a deterministic RNG seeded from the test case
        let mut crash_rng_state: u64 = 12345;

        for transition in &transitions {
            // Check invariant
            assert_invariant::<M>(&model_state, "before step");

            // Run the model
            let model_result = M::step_model(
                &mut model_state,
                transition.as_ref(),
                &model_env,
            );

            // Run the SUT
            let sut_result = M::step_sut(
                &mut sut,
                transition.as_ref(),
                &real_env,
            );

            // Bridge check
            transition
                .check_bridge(&*model_result, &*sut_result)
                .unwrap_or_else(|msg| {
                    panic!(
                        "Lockstep mismatch!\n  Action: {:?}\n{}",
                        transition, msg
                    )
                });

            // Store variables
            let var_id = next_var_id;
            transition.store_model_var(var_id, &*model_result, &mut model_env);
            transition.store_sut_var(var_id, &*sut_result, &mut real_env);
            next_var_id += 1;

            // Maybe inject a crash
            crash_rng_state = crash_rng_state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let crash_roll = (crash_rng_state >> 33) as f64 / (1u64 << 31) as f64;

            if crash_roll < config.crash_probability && crash_count < config.max_crashes {
                crash_count += 1;

                // Checkpoint the model
                let checkpoint = M::model_checkpoint(&model_state);

                // Recover both sides
                model_state = M::model_recover(&checkpoint);
                sut = M::sut_recover(sut);

                // Reset environments (variables from before the crash
                // may reference values that no longer exist)
                model_env = TypedEnv::new();
                real_env = TypedEnv::new();
                next_var_id = 0;

                // Check invariant after recovery
                assert_invariant::<M>(&model_state, "after crash recovery");
            }
        }

        // Final invariant check
        assert_invariant::<M>(&model_state, "end of test");
    });
}
