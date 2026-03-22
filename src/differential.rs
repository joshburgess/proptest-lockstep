//! Differential bridge testing.
//!
//! Given two bridges for the same action — a coarser one (user's) and
//! a finer one (auto-generated) — this module detects when the coarser
//! bridge hides real bugs that the finer bridge would catch.
//!
//! The theoretical foundation is `refines_strengthen_bisim`: a finer
//! bridge gives a strictly stronger guarantee. The contrapositive:
//! if a test passes with the coarse bridge but FAILS with the fine
//! bridge, the coarse bridge is masking a real discrepancy.
//!
//! # Use Cases
//!
//! - Detect overly-coarse `Opaque` bridges that should be `Transparent`
//! - Audit bridge precision: are you testing as much as you could be?
//! - Catch "hidden bugs" where handles/IDs differ but the test passes
//!   because the bridge doesn't observe the difference
//!
//! # How It Works
//!
//! 1. Run actions against model and SUT
//! 2. Check the user's bridge (coarse) — record pass/fail
//! 3. Check the finest possible bridge (all Transparent where types
//!    match) — record pass/fail
//! 4. If fine fails but coarse passes: report a **bridge weakness**
//!
//! This is a meta-testing technique: testing the test oracles themselves.

use std::any::Any;
use std::fmt::Debug;

use proptest_state_machine::ReferenceStateMachine;

use crate::action::AnyAction;
use crate::env::TypedEnv;
use crate::model::LockstepModel;
use crate::runner::LockstepRef;

// ---------------------------------------------------------------------------
// Trait
// ---------------------------------------------------------------------------

/// Extension trait for lockstep models with differential bridge testing.
///
/// Users provide a `fine_check` method that performs a stricter bridge
/// check than the default. The framework runs both checks and reports
/// discrepancies where the coarse bridge passes but the fine bridge fails.
pub trait DifferentialBridgeModel: LockstepModel {
    /// Perform a fine-grained bridge check on the action's results.
    ///
    /// This should be stricter than the default bridge — for example,
    /// using `Transparent` where the default uses `Opaque`. Returns
    /// `Ok(())` if the fine check passes, or an error message.
    ///
    /// The framework compares this with the default `check_bridge`:
    /// - Both pass → no issue
    /// - Both fail → genuine bug (detected by both)
    /// - Fine fails, coarse passes → **bridge weakness** (reported)
    /// - Fine passes, coarse fails → impossible (fine is stricter)
    fn fine_check(
        action: &dyn AnyAction,
        model_result: &dyn Any,
        sut_result: &dyn Any,
    ) -> Result<(), String>;
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for differential bridge testing.
#[derive(Debug, Clone)]
pub struct DifferentialConfig {
    /// Number of proptest cases.
    pub cases: u32,
    /// Sequence length range.
    pub min_ops: usize,
    pub max_ops: usize,
    /// Whether to panic on bridge weakness (default: true).
    /// Set to false to collect weaknesses without failing.
    pub fail_on_weakness: bool,
}

impl Default for DifferentialConfig {
    fn default() -> Self {
        DifferentialConfig {
            cases: 100,
            min_ops: 5,
            max_ops: 30,
            fail_on_weakness: true,
        }
    }
}

// ---------------------------------------------------------------------------
// Results
// ---------------------------------------------------------------------------

/// A bridge weakness: the coarse bridge passed but the fine bridge failed.
#[derive(Debug, Clone)]
pub struct BridgeWeakness {
    /// Which step in the trace triggered the weakness.
    pub step: usize,
    /// Description of the action.
    pub action: String,
    /// The fine bridge's error message.
    pub fine_error: String,
}

/// Summary of a differential bridge test run.
#[derive(Debug, Clone, Default)]
pub struct DifferentialStats {
    /// Number of steps checked.
    pub steps_checked: usize,
    /// Number of steps where both bridges agreed (both pass or both fail).
    pub agreements: usize,
    /// Number of bridge weaknesses found.
    pub weaknesses_found: usize,
}

impl std::fmt::Display for DifferentialStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Differential bridge testing: {} steps checked, {} agreements, {} weaknesses found",
            self.steps_checked, self.agreements, self.weaknesses_found,
        )
    }
}

// ---------------------------------------------------------------------------
// Runner
// ---------------------------------------------------------------------------

/// Run a differential bridge test.
///
/// At each step, runs both the coarse bridge (default `check_bridge`)
/// and the fine bridge (`fine_check`). Reports bridge weaknesses where
/// the coarse bridge passes but the fine bridge fails.
///
/// # Panics
///
/// - If `fail_on_weakness` is true and a bridge weakness is found
/// - If the coarse bridge fails (this is a normal lockstep mismatch)
pub fn run_differential_test<M: DifferentialBridgeModel>(
    config: DifferentialConfig,
) -> DifferentialStats {
    let proptest_config = proptest::test_runner::Config {
        cases: config.cases,
        ..Default::default()
    };

    let size = config.min_ops..config.max_ops;
    let total_stats = std::sync::Mutex::new(DifferentialStats::default());

    proptest::proptest!(proptest_config, |((_initial_state, transitions, _seen_counter) in
        <LockstepRef<M> as ReferenceStateMachine>::sequential_strategy(size))| {

        let mut model_state = M::init_model();
        let mut sut = M::init_sut();
        let mut model_env = TypedEnv::new();
        let mut real_env = TypedEnv::new();
        let mut next_var_id: usize = 0;

        for (step, transition) in transitions.iter().enumerate() {
            // Run model
            let model_result = M::step_model(
                &mut model_state,
                transition.as_ref(),
                &model_env,
            );

            // Run SUT
            let sut_result = M::step_sut(
                &mut sut,
                transition.as_ref(),
                &real_env,
            );

            // Coarse bridge check (default)
            let coarse = transition.check_bridge(&*model_result, &*sut_result);

            // Fine bridge check
            let fine = M::fine_check(
                transition.as_ref(),
                &*model_result,
                &*sut_result,
            );

            total_stats.lock().unwrap().steps_checked += 1;

            match (&coarse, &fine) {
                (Ok(()), Ok(())) => {
                    // Both pass — no issue
                    total_stats.lock().unwrap().agreements += 1;
                }
                (Err(msg), _) => {
                    // Coarse fails — this is a real lockstep mismatch
                    total_stats.lock().unwrap().agreements += 1;
                    panic!(
                        "Lockstep mismatch!\n  Action: {:?}\n{}",
                        transition, msg
                    );
                }
                (Ok(()), Err(fine_msg)) => {
                    // BRIDGE WEAKNESS: coarse passes but fine fails
                    total_stats.lock().unwrap().weaknesses_found += 1;

                    if config.fail_on_weakness {
                        panic!(
                            "Bridge weakness detected at step {}!\n\
                             The default (coarse) bridge passed, but a finer bridge failed.\n\
                             This means your bridge is hiding a real discrepancy.\n\n\
                             Action: {:?}\n\
                             Fine bridge error:\n{}\n\n\
                             Consider using a more precise bridge for this action.",
                            step, transition, fine_msg
                        );
                    }
                }
            }

            // Store variables
            let var_id = next_var_id;
            transition.store_model_var(var_id, &*model_result, &mut model_env);
            transition.store_sut_var(var_id, &*sut_result, &mut real_env);
            next_var_id += 1;
        }
    });

    total_stats.into_inner().unwrap()
}
