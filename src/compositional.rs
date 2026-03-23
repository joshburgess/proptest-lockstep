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

// ---------------------------------------------------------------------------
// Incremental compositional testing
// ---------------------------------------------------------------------------

/// Tracks incremental testing state for composed systems.
///
/// When you have a composed system (subsystem A + subsystem B) and
/// refine one subsystem's bridges, you only need to re-test that
/// subsystem. The other subsystem's previous test result carries over.
///
/// This is justified by `product_bisim_iff` and `product_refines_bisim`
/// in `Compositional.lean`: product bisimulation is equivalent to both
/// components satisfying bisimulation independently, and bridge
/// refinement on one component doesn't affect the other.
///
/// # Example
///
/// ```text
/// let mut comp = IncrementalComposition::new();
///
/// // Initial testing: test both subsystems
/// comp.test_left::<Counter>(1..20);     // Counter passes
/// comp.test_right::<Logger>(1..20);     // Logger passes
/// assert!(comp.is_sound());             // Composition is sound
///
/// // Later: refine Logger's bridges from Opaque to Transparent
/// // Only need to re-test Logger; Counter's result is reused
/// comp.retest_right::<Logger>(1..20);   // Re-test Logger only
/// assert!(comp.is_sound());             // Still sound
/// ```
#[derive(Debug, Clone)]
pub struct IncrementalComposition {
    left_verified: bool,
    right_verified: bool,
    left_traces_tested: usize,
    right_traces_tested: usize,
}

impl IncrementalComposition {
    /// Create a new incremental composition tracker.
    /// Neither subsystem is verified yet.
    pub fn new() -> Self {
        IncrementalComposition {
            left_verified: false,
            right_verified: false,
            left_traces_tested: 0,
            right_traces_tested: 0,
        }
    }

    /// Test only the left subsystem. Marks it as verified if all tests pass.
    ///
    /// The right subsystem's previous result (if any) is preserved.
    /// This is justified by `product_bisim_iff`: the product passes
    /// iff both components pass independently.
    pub fn test_left<L: LockstepModel>(&mut self, size: std::ops::Range<usize>) {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            crate::runner::run_lockstep_test::<L>(size.clone());
        }));
        self.left_verified = result.is_ok();
        self.left_traces_tested += 1;
    }

    /// Test only the right subsystem. Marks it as verified if all tests pass.
    ///
    /// The left subsystem's previous result (if any) is preserved.
    pub fn test_right<R: LockstepModel>(&mut self, size: std::ops::Range<usize>) {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            crate::runner::run_lockstep_test::<R>(size.clone());
        }));
        self.right_verified = result.is_ok();
        self.right_traces_tested += 1;
    }

    /// Re-test the left subsystem after a change (e.g., bridge refinement).
    ///
    /// The right subsystem's previous result is reused — this is the
    /// incremental guarantee from `product_refines_bisim`: refining
    /// one component's bridges doesn't invalidate the other component's
    /// test results.
    pub fn retest_left<L: LockstepModel>(&mut self, size: std::ops::Range<usize>) {
        self.test_left::<L>(size);
    }

    /// Re-test the right subsystem after a change.
    ///
    /// The left subsystem's previous result is reused.
    pub fn retest_right<R: LockstepModel>(&mut self, size: std::ops::Range<usize>) {
        self.test_right::<R>(size);
    }

    /// Invalidate the left subsystem's result (e.g., after changing its
    /// implementation). Forces re-testing before the composition is sound.
    pub fn invalidate_left(&mut self) {
        self.left_verified = false;
    }

    /// Invalidate the right subsystem's result.
    pub fn invalidate_right(&mut self) {
        self.right_verified = false;
    }

    /// Whether the composition is sound: both subsystems have been
    /// verified independently.
    ///
    /// By `product_bisim_iff` (Compositional.lean), the product
    /// satisfies bounded bisimulation iff both components do.
    pub fn is_sound(&self) -> bool {
        self.left_verified && self.right_verified
    }

    /// Get the detailed result.
    pub fn result(&self) -> IncrementalResult {
        IncrementalResult {
            left_verified: self.left_verified,
            right_verified: self.right_verified,
            composition_sound: self.is_sound(),
            left_tests_run: self.left_traces_tested,
            right_tests_run: self.right_traces_tested,
        }
    }
}

impl Default for IncrementalComposition {
    fn default() -> Self {
        Self::new()
    }
}

/// Result of incremental compositional verification.
#[derive(Debug, Clone)]
pub struct IncrementalResult {
    /// Whether the left subsystem has been verified.
    pub left_verified: bool,
    /// Whether the right subsystem has been verified.
    pub right_verified: bool,
    /// Whether the composition is sound (both verified).
    pub composition_sound: bool,
    /// Total number of test runs for the left subsystem.
    pub left_tests_run: usize,
    /// Total number of test runs for the right subsystem.
    pub right_tests_run: usize,
}

impl std::fmt::Display for IncrementalResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Incremental composition: left={} ({}x), right={} ({}x), composed={}",
            if self.left_verified { "PASS" } else { "PENDING" },
            self.left_tests_run,
            if self.right_verified { "PASS" } else { "PENDING" },
            self.right_tests_run,
            if self.composition_sound { "SOUND" } else { "INCOMPLETE" },
        )
    }
}
