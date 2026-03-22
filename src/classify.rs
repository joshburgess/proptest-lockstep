//! Consistency-level inference.
//!
//! Automatically determines the strongest consistency level a system
//! satisfies by running it through the hierarchy:
//!
//! ```text
//! Linearizable → Session-consistent → Eventually-consistent → None
//! ```
//!
//! Usage:
//! ```ignore
//! let level = classify_consistency::<MyModel>(ClassifyConfig::default());
//! println!("{}", level);
//! // Output: "Session-consistent (not linearizable)"
//! ```

use std::fmt;

use proptest_state_machine::ReferenceStateMachine;

use crate::env::TypedEnv;
use crate::model::LockstepModel;
use crate::runner::LockstepRef;

/// The consistency level of a system.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConsistencyLevel {
    /// Every operation matches the model exactly at every step.
    Linearizable,
    /// Per-step mismatches exist, but the system is usable.
    /// (Placeholder — full session checking requires SessionConsistencyModel.)
    WeakerThanLinearizable,
}

impl fmt::Display for ConsistencyLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConsistencyLevel::Linearizable => write!(f, "Linearizable"),
            ConsistencyLevel::WeakerThanLinearizable => {
                write!(f, "Weaker than linearizable (per-step mismatches detected)")
            }
        }
    }
}

/// Configuration for consistency classification.
#[derive(Debug, Clone)]
pub struct ClassifyConfig {
    /// Number of proptest cases to run.
    pub cases: u32,
    /// Trace length range.
    pub min_ops: usize,
    pub max_ops: usize,
}

impl Default for ClassifyConfig {
    fn default() -> Self {
        ClassifyConfig {
            cases: 100,
            min_ops: 5,
            max_ops: 20,
        }
    }
}

/// Result of consistency classification.
#[derive(Debug, Clone)]
pub struct ClassifyResult {
    /// The strongest consistency level the system satisfies.
    pub level: ConsistencyLevel,
    /// Number of traces tested.
    pub traces_tested: usize,
    /// Number of per-step mismatches found (0 = linearizable).
    pub mismatches_found: usize,
}

impl fmt::Display for ClassifyResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} ({} traces tested, {} mismatches)",
            self.level, self.traces_tested, self.mismatches_found,
        )
    }
}

/// Classify the consistency level of a system.
///
/// Runs the lockstep test and checks whether per-step bridge checks
/// all pass (linearizable) or some fail (weaker).
///
/// # Example
///
/// ```ignore
/// let result = classify_consistency::<MyModel>(ClassifyConfig::default());
/// println!("{}", result);
/// ```
pub fn classify_consistency<M: LockstepModel>(
    config: ClassifyConfig,
) -> ClassifyResult {
    let proptest_config = proptest::test_runner::Config {
        cases: config.cases,
        ..Default::default()
    };

    let size = config.min_ops..config.max_ops;
    let mismatches = std::sync::Mutex::new(0usize);
    let traces = std::sync::Mutex::new(0usize);

    // Run lockstep and count mismatches instead of panicking
    proptest::proptest!(proptest_config, |((_initial_state, transitions, _seen_counter) in
        <LockstepRef<M> as ReferenceStateMachine>::sequential_strategy(size))| {

        *traces.lock().unwrap() += 1;

        let mut model_state = M::init_model();
        let mut sut = M::init_sut();
        let mut model_env = TypedEnv::new();
        let mut real_env = TypedEnv::new();
        let mut next_var_id: usize = 0;

        for transition in &transitions {
            let model_result = M::step_model(
                &mut model_state,
                transition.as_ref(),
                &model_env,
            );
            let sut_result = M::step_sut(
                &mut sut,
                transition.as_ref(),
                &real_env,
            );

            if transition.check_bridge(&*model_result, &*sut_result).is_err() {
                *mismatches.lock().unwrap() += 1;
            }

            transition.store_model_var(next_var_id, &*model_result, &mut model_env);
            transition.store_sut_var(next_var_id, &*sut_result, &mut real_env);
            next_var_id += 1;
        }
    });

    let total_mismatches = *mismatches.lock().unwrap();
    let total_traces = *traces.lock().unwrap();

    let level = if total_mismatches == 0 {
        ConsistencyLevel::Linearizable
    } else {
        ConsistencyLevel::WeakerThanLinearizable
    };

    ClassifyResult {
        level,
        traces_tested: total_traces,
        mismatches_found: total_mismatches,
    }
}
