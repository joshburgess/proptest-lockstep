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
//! records any mismatch. At the end, `report` summarizes all
//! violations.

use std::any::Any;
use std::fmt::Debug;

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
// Refinement Guard
// ---------------------------------------------------------------------------

/// A runtime refinement guard that shadows the SUT with a model.
///
/// At each operation, the guard runs the model in parallel and checks
/// bridge equivalence. Violations are collected (not panicked on),
/// allowing the SUT to continue operating.
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
/// ```
pub struct RefinementGuard<M: LockstepModel> {
    model_state: M::ModelState,
    model_env: TypedEnv,
    next_var_id: usize,
    step: usize,
    violations: Vec<ContractViolation>,
    checks_passed: usize,
}

impl<M: LockstepModel> RefinementGuard<M> {
    /// Create a new refinement guard with a fresh model.
    pub fn new() -> Self {
        RefinementGuard {
            model_state: M::init_model(),
            model_env: TypedEnv::new(),
            next_var_id: 0,
            step: 0,
            violations: Vec::new(),
            checks_passed: 0,
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
        }
    }

    /// Check an operation against the model.
    ///
    /// Runs the model with the same action, compares results via
    /// bridge, and records any violation. The SUT result is passed
    /// in — the guard doesn't execute the SUT, only the model.
    pub fn check(
        &mut self,
        action: &dyn AnyAction,
        sut_result: &dyn Any,
    ) {
        // Run the model
        let model_result = M::step_model(
            &mut self.model_state,
            action,
            &self.model_env,
        );

        // Bridge check
        match action.check_bridge(&*model_result, sut_result) {
            Ok(()) => {
                self.checks_passed += 1;
            }
            Err(msg) => {
                self.violations.push(ContractViolation {
                    step: self.step,
                    action_desc: format!("{:?}", action),
                    mismatch: msg,
                });
            }
        }

        // Store model variables
        action.store_model_var(self.next_var_id, &*model_result, &mut self.model_env);
        self.next_var_id += 1;
        self.step += 1;
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

    /// Total number of checks performed.
    pub fn total_checks(&self) -> usize {
        self.step
    }

    /// Get all violations.
    pub fn violations(&self) -> &[ContractViolation] {
        &self.violations
    }

    /// Get a reference to the current model state.
    pub fn model_state(&self) -> &M::ModelState {
        &self.model_state
    }

    /// Generate a human-readable violation report.
    pub fn report(&self) -> String {
        if self.violations.is_empty() {
            format!(
                "Refinement contract: {} checks passed, 0 violations",
                self.checks_passed,
            )
        } else {
            let mut report = format!(
                "Refinement contract: {} violations in {} checks ({} passed)\n\n",
                self.violations.len(),
                self.step,
                self.checks_passed,
            );
            for v in &self.violations {
                report.push_str(&format!("{}\n", v));
            }
            report
        }
    }

    /// Reset the guard (clear violations, restart model).
    pub fn reset(&mut self) {
        self.model_state = M::init_model();
        self.model_env = TypedEnv::new();
        self.next_var_id = 0;
        self.step = 0;
        self.violations.clear();
        self.checks_passed = 0;
    }
}

impl<M: LockstepModel> Debug for RefinementGuard<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RefinementGuard")
            .field("step", &self.step)
            .field("violations", &self.violations.len())
            .field("checks_passed", &self.checks_passed)
            .finish()
    }
}

// ---------------------------------------------------------------------------
// Convenience: assert no violations
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
