//! Observational refinement contracts.
//!
//! Turns the bridge algebra into a **runtime contract system**: the
//! model runs as a shadow alongside the SUT, and bridge checks are
//! performed at every operation boundary. Violations are reported
//! as contract failures rather than panics, enabling use in
//! production-adjacent environments (staging, canary deployments,
//! integration tests).
//!
//! This bridges testing and production monitoring: the same bridge
//! algebra that powers lockstep testing also powers runtime
//! verification. The `observational_refinement_equiv` theorem
//! guarantees the contract is *exactly right* — it catches all
//! bugs detectable by the bridge and nothing more.
//!
//! # Use Cases
//!
//! - **Shadow testing**: run the model alongside production, log
//!   mismatches without failing
//! - **Canary validation**: check new deployments against the model
//!   before full rollout
//! - **Regression detection**: catch behavioral changes between
//!   versions by comparing against the model
//! - **Gradual verification**: start with `Opaque` bridges (no
//!   checking) and progressively tighten to `Transparent`
//!
//! # Architecture
//!
//! The [`RefinementGuard`] wraps a model state and tracks violations.
//! Each call to `check` runs the model, compares via bridge, and
//! records any mismatch.
//!
//! Features:
//! - **Performance tracking**: measures model execution and bridge
//!   check overhead per operation
//! - **Divergence handling**: after a violation, the model and SUT
//!   may be in different states; configurable recovery strategies
//! - **Partial monitoring**: check only a subset of operations via
//!   a sampling rate, reducing overhead in production

use std::any::Any;
use std::fmt::Debug;
use std::time::{Duration, Instant};

use crate::action::AnyAction;
use crate::env::TypedEnv;
use crate::model::LockstepModel;

// ---------------------------------------------------------------------------
// Violation
// ---------------------------------------------------------------------------

/// A single refinement contract violation.
#[derive(Debug, Clone)]
pub struct ContractViolation {
    /// Which step triggered the violation.
    pub step: usize,
    /// Description of the action.
    pub action_desc: String,
    /// The bridge mismatch message.
    pub mismatch: String,
}

impl std::fmt::Display for ContractViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "  [step {}] {}\n{}",
            self.step, self.action_desc, self.mismatch,
        )
    }
}

// ---------------------------------------------------------------------------
// Divergence strategy
// ---------------------------------------------------------------------------

/// What to do when a violation is detected and the model/SUT may
/// have diverged.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DivergenceStrategy {
    /// Continue monitoring — the model and SUT may be out of sync,
    /// but subsequent violations are still reported. Use when you
    /// want to collect ALL mismatches, even after divergence.
    Continue,
    /// Stop monitoring after the first violation. Use when the first
    /// mismatch makes subsequent checks meaningless (because the
    /// model state is now wrong).
    StopOnFirst,
    /// Reset the model to its initial state after each violation.
    /// Use when individual operations are independent and you want
    /// to catch per-operation bugs without accumulating state drift.
    ResetOnViolation,
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for refinement contract monitoring.
#[derive(Debug, Clone)]
pub struct ContractConfig {
    /// How to handle divergence after a violation. Default: `Continue`.
    pub divergence: DivergenceStrategy,
    /// Sampling rate: probability of checking each operation (0.0 to 1.0).
    /// 1.0 = check every operation (default). 0.1 = check ~10% of operations.
    /// Use < 1.0 to reduce overhead in production.
    pub sampling_rate: f64,
    /// Maximum number of violations to record before stopping.
    /// 0 = unlimited (default).
    pub max_violations: usize,
}

impl Default for ContractConfig {
    fn default() -> Self {
        ContractConfig {
            divergence: DivergenceStrategy::Continue,
            sampling_rate: 1.0,
            max_violations: 0,
        }
    }
}

// ---------------------------------------------------------------------------
// Performance stats
// ---------------------------------------------------------------------------

/// Performance statistics for the refinement guard.
#[derive(Debug, Clone, Default)]
pub struct ContractPerformance {
    /// Total time spent running the model.
    pub model_time: Duration,
    /// Total time spent on bridge checks.
    pub bridge_time: Duration,
    /// Number of operations checked.
    pub operations_checked: usize,
    /// Number of operations skipped (due to sampling).
    pub operations_skipped: usize,
}

impl ContractPerformance {
    /// Average model execution time per checked operation.
    pub fn avg_model_time(&self) -> Duration {
        if self.operations_checked > 0 {
            self.model_time / self.operations_checked as u32
        } else {
            Duration::ZERO
        }
    }

    /// Average bridge check time per checked operation.
    pub fn avg_bridge_time(&self) -> Duration {
        if self.operations_checked > 0 {
            self.bridge_time / self.operations_checked as u32
        } else {
            Duration::ZERO
        }
    }

    /// Total overhead (model + bridge) as a duration.
    pub fn total_overhead(&self) -> Duration {
        self.model_time + self.bridge_time
    }
}

impl std::fmt::Display for ContractPerformance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Contract performance: {} checked, {} skipped, \
             model={:?} (avg {:?}), bridge={:?} (avg {:?}), \
             total overhead={:?}",
            self.operations_checked,
            self.operations_skipped,
            self.model_time,
            self.avg_model_time(),
            self.bridge_time,
            self.avg_bridge_time(),
            self.total_overhead(),
        )
    }
}

// ---------------------------------------------------------------------------
// Refinement Guard
// ---------------------------------------------------------------------------

/// A runtime refinement guard that shadows the SUT with a model.
///
/// At each operation, the guard runs the model in parallel and checks
/// bridge equivalence. Violations are collected (not panicked on),
/// allowing the SUT to continue operating.
///
/// Features:
/// - **Performance tracking**: measures model and bridge check overhead
/// - **Divergence handling**: configurable behavior after violations
/// - **Partial monitoring**: sampling rate for production use
///
/// # Example
///
/// ```ignore
/// let mut guard = RefinementGuard::<MyModel>::new();
///
/// // For each operation in production:
/// let sut_result = my_sut.do_something(args);
/// guard.check(&action, &sut_result);
///
/// // At the end (or periodically):
/// if guard.has_violations() {
///     eprintln!("{}", guard.report());
/// }
/// eprintln!("{}", guard.performance());
/// ```
pub struct RefinementGuard<M: LockstepModel> {
    model_state: M::ModelState,
    model_env: TypedEnv,
    next_var_id: usize,
    step: usize,
    violations: Vec<ContractViolation>,
    checks_passed: usize,
    config: ContractConfig,
    perf: ContractPerformance,
    stopped: bool,
    rng_state: u64,
}

impl<M: LockstepModel> RefinementGuard<M> {
    /// Create a new refinement guard with default configuration.
    pub fn new() -> Self {
        Self::with_config(ContractConfig::default())
    }

    /// Create a refinement guard with custom configuration.
    pub fn with_config(config: ContractConfig) -> Self {
        RefinementGuard {
            model_state: M::init_model(),
            model_env: TypedEnv::new(),
            next_var_id: 0,
            step: 0,
            violations: Vec::new(),
            checks_passed: 0,
            config,
            perf: ContractPerformance::default(),
            stopped: false,
            rng_state: 42,
        }
    }

    /// Create a refinement guard with a specific initial model state.
    pub fn with_model(model_state: M::ModelState) -> Self {
        RefinementGuard {
            model_state,
            model_env: TypedEnv::new(),
            next_var_id: 0,
            step: 0,
            violations: Vec::new(),
            checks_passed: 0,
            config: ContractConfig::default(),
            perf: ContractPerformance::default(),
            stopped: false,
            rng_state: 42,
        }
    }

    /// Check an operation against the model.
    ///
    /// Runs the model with the same action, compares results via
    /// bridge, and records any violation. Respects sampling rate
    /// and divergence strategy.
    pub fn check(
        &mut self,
        action: &dyn AnyAction,
        sut_result: &dyn Any,
    ) {
        self.step += 1;

        // Check if monitoring has been stopped
        if self.stopped {
            self.perf.operations_skipped += 1;
            return;
        }

        // Check violation limit
        if self.config.max_violations > 0
            && self.violations.len() >= self.config.max_violations
        {
            self.perf.operations_skipped += 1;
            return;
        }

        // Sampling: skip this operation with probability (1 - sampling_rate)
        if self.config.sampling_rate < 1.0 {
            self.rng_state = self.rng_state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let roll = (self.rng_state >> 33) as f64 / (1u64 << 31) as f64;
            if roll >= self.config.sampling_rate {
                self.perf.operations_skipped += 1;
                // Still step the model to keep it in sync
                let model_result = M::step_model(
                    &mut self.model_state,
                    action,
                    &self.model_env,
                );
                action.store_model_var(self.next_var_id, &*model_result, &mut self.model_env);
                self.next_var_id += 1;
                return;
            }
        }

        // Run the model (timed)
        let model_start = Instant::now();
        let model_result = M::step_model(
            &mut self.model_state,
            action,
            &self.model_env,
        );
        self.perf.model_time += model_start.elapsed();

        // Bridge check (timed)
        let bridge_start = Instant::now();
        let bridge_result = action.check_bridge(&*model_result, sut_result);
        self.perf.bridge_time += bridge_start.elapsed();

        self.perf.operations_checked += 1;

        match bridge_result {
            Ok(()) => {
                self.checks_passed += 1;
            }
            Err(msg) => {
                self.violations.push(ContractViolation {
                    step: self.step,
                    action_desc: format!("{:?}", action),
                    mismatch: msg,
                });

                // Handle divergence
                match self.config.divergence {
                    DivergenceStrategy::Continue => {}
                    DivergenceStrategy::StopOnFirst => {
                        self.stopped = true;
                    }
                    DivergenceStrategy::ResetOnViolation => {
                        self.model_state = M::init_model();
                        self.model_env = TypedEnv::new();
                        self.next_var_id = 0;
                    }
                }
            }
        }

        // Store model variables (unless we just reset)
        if !matches!(self.config.divergence, DivergenceStrategy::ResetOnViolation)
            || self.violations.last().map_or(true, |v| v.step != self.step)
        {
            action.store_model_var(self.next_var_id, &*model_result, &mut self.model_env);
            self.next_var_id += 1;
        }
    }

    /// Whether any violations have been recorded.
    pub fn has_violations(&self) -> bool {
        !self.violations.is_empty()
    }

    /// Number of violations recorded.
    pub fn violation_count(&self) -> usize {
        self.violations.len()
    }

    /// Number of checks that passed.
    pub fn checks_passed(&self) -> usize {
        self.checks_passed
    }

    /// Total number of steps (including skipped).
    pub fn total_steps(&self) -> usize {
        self.step
    }

    /// Whether monitoring has been stopped (due to StopOnFirst or max_violations).
    pub fn is_stopped(&self) -> bool {
        self.stopped
    }

    /// Get all violations.
    pub fn violations(&self) -> &[ContractViolation] {
        &self.violations
    }

    /// Get a reference to the current model state.
    pub fn model_state(&self) -> &M::ModelState {
        &self.model_state
    }

    /// Get performance statistics.
    pub fn performance(&self) -> &ContractPerformance {
        &self.perf
    }

    /// Generate a human-readable violation report.
    pub fn report(&self) -> String {
        let mut report = if self.violations.is_empty() {
            format!(
                "Refinement contract: {} checks passed, 0 violations",
                self.checks_passed,
            )
        } else {
            format!(
                "Refinement contract: {} violations in {} steps ({} checked, {} skipped, {} passed)\n\n",
                self.violations.len(),
                self.step,
                self.perf.operations_checked,
                self.perf.operations_skipped,
                self.checks_passed,
            )
        };

        for v in &self.violations {
            report.push_str(&format!("{}\n", v));
        }

        if self.stopped {
            report.push_str("\n[monitoring stopped]\n");
        }

        report
    }

    /// Reset the guard (clear violations, restart model).
    pub fn reset(&mut self) {
        self.model_state = M::init_model();
        self.model_env = TypedEnv::new();
        self.next_var_id = 0;
        self.step = 0;
        self.violations.clear();
        self.checks_passed = 0;
        self.perf = ContractPerformance::default();
        self.stopped = false;
    }
}

impl<M: LockstepModel> Debug for RefinementGuard<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RefinementGuard")
            .field("step", &self.step)
            .field("violations", &self.violations.len())
            .field("checks_passed", &self.checks_passed)
            .field("stopped", &self.stopped)
            .field("sampling_rate", &self.config.sampling_rate)
            .finish()
    }
}

// ---------------------------------------------------------------------------
// Convenience
// ---------------------------------------------------------------------------

/// Assert that a refinement guard has no violations.
///
/// Panics with a detailed report if any violations exist.
pub fn assert_no_violations<M: LockstepModel>(guard: &RefinementGuard<M>) {
    if guard.has_violations() {
        panic!(
            "Refinement contract violated!\n\n{}",
            guard.report(),
        );
    }
}
