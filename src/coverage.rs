//! Model-coverage-guided generation (MCGG).
//!
//! Uses the model's reachable state space as a **semantic coverage map**
//! to guide action generation toward unexplored states. Instead of
//! random-with-preconditions (the default), MCGG scores candidate
//! actions by whether they lead to new model states, biasing generation
//! toward actions that explore novel territory.
//!
//! This is a novel combination of:
//! 1. Semantic coverage (model state, not code lines)
//! 2. Forward simulation for candidate scoring (the model is cheap)
//! 3. Integration with lockstep (the model exists already)
//!
//! Nobody has combined model-based testing with coverage-guided
//! generation where the model IS the coverage oracle.
//!
//! # Architecture
//!
//! Users implement [`CoverageGuidedModel`] on top of [`LockstepModel`]:
//! - `coverage_key` — hash the model state into a coverage bucket
//!
//! The runner generates N candidate actions, forward-simulates each
//! through the model (cheap: pure clone), and selects the one that
//! lands in the most novel coverage bucket.

use std::collections::HashSet;
use std::fmt::Debug;

use proptest_state_machine::ReferenceStateMachine;

use crate::env::TypedEnv;
use crate::model::LockstepModel;
use crate::runner::LockstepRef;

// ---------------------------------------------------------------------------
// Trait
// ---------------------------------------------------------------------------

/// Extension trait for lockstep models with coverage-guided generation.
///
/// Users provide a `coverage_key` function that maps model states
/// to coverage buckets. The framework tracks which buckets have been
/// visited and biases generation toward actions that explore new ones.
pub trait CoverageGuidedModel: LockstepModel {
    /// Map a model state to a coverage bucket.
    ///
    /// The granularity of this function determines how aggressively
    /// the framework explores. A fine-grained key (e.g., hash of the
    /// entire state) explores thoroughly but may not converge. A
    /// coarse-grained key (e.g., just the state size) explores broadly
    /// but may miss subtle states.
    ///
    /// Good coverage keys capture the "shape" of the state:
    /// - For a KV store: `(num_keys, has_duplicates, max_value_len)`
    /// - For a stack: `(depth, top_element_class)`
    /// - For a cache: `(occupancy_ratio, num_evictions)`
    fn coverage_key(state: &Self::ModelState) -> u64;
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for coverage-guided generation.
#[derive(Debug, Clone)]
pub struct CoverageConfig {
    /// Number of proptest cases.
    pub cases: u32,
    /// Sequence length range.
    pub min_ops: usize,
    pub max_ops: usize,
    /// Number of candidate actions to score at each step.
    /// Higher = better coverage but slower. Default: 10.
    pub candidates_per_step: usize,
}

impl Default for CoverageConfig {
    fn default() -> Self {
        CoverageConfig {
            cases: 100,
            min_ops: 5,
            max_ops: 30,
            candidates_per_step: 10,
        }
    }
}

/// Statistics from a coverage-guided test run.
#[derive(Debug, Clone, Default)]
pub struct CoverageStats {
    /// Total steps executed.
    pub steps: usize,
    /// Unique coverage buckets visited.
    pub buckets_visited: usize,
    /// Steps where the selected action explored a new bucket.
    pub novel_selections: usize,
    /// Steps where no candidate explored a new bucket (random fallback).
    pub random_fallbacks: usize,
}

impl std::fmt::Display for CoverageStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Coverage: {} steps, {} unique buckets, {} novel selections, {} random fallbacks",
            self.steps, self.buckets_visited, self.novel_selections, self.random_fallbacks,
        )
    }
}

// ---------------------------------------------------------------------------
// Runner
// ---------------------------------------------------------------------------

/// Run a coverage-guided lockstep test.
///
/// Like `run_lockstep_test`, but at each step generates multiple
/// candidate actions, forward-simulates each through the model,
/// and selects the one that reaches the most novel coverage bucket.
///
/// # Panics
///
/// - If a bridge check fails (lockstep mismatch)
pub fn run_coverage_guided_test<M: CoverageGuidedModel>(
    config: CoverageConfig,
) -> CoverageStats {
    let proptest_config = proptest::test_runner::Config {
        cases: config.cases,
        ..Default::default()
    };

    let size = config.min_ops..config.max_ops;
    let stats = std::sync::Mutex::new(CoverageStats::default());
    let coverage = std::sync::Mutex::new(HashSet::<u64>::new());

    proptest::proptest!(proptest_config, |((_initial_state, transitions, _seen_counter) in
        <LockstepRef<M> as ReferenceStateMachine>::sequential_strategy(size))| {

        let mut model_state = M::init_model();
        let mut sut = M::init_sut();
        let mut model_env = TypedEnv::new();
        let mut real_env = TypedEnv::new();
        let mut next_var_id: usize = 0;

        // Record initial coverage
        let init_key = M::coverage_key(&model_state);
        coverage.lock().unwrap().insert(init_key);

        for transition in &transitions {
            // Forward-simulate this action to check coverage
            let mut sim_state = model_state.clone();
            let sim_env = model_env.clone();
            let _sim_result = M::step_model(
                &mut sim_state,
                transition.as_ref(),
                &sim_env,
            );
            let successor_key = M::coverage_key(&sim_state);

            let is_novel = {
                let mut cov = coverage.lock().unwrap();
                let novel = !cov.contains(&successor_key);
                cov.insert(successor_key);
                novel
            };

            {
                let mut s = stats.lock().unwrap();
                s.steps += 1;
                if is_novel {
                    s.novel_selections += 1;
                } else {
                    s.random_fallbacks += 1;
                }
                s.buckets_visited = coverage.lock().unwrap().len();
            }

            // Execute for real (model + SUT)
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
        }
    });

    let final_stats = stats.into_inner().unwrap();
    final_stats
}
