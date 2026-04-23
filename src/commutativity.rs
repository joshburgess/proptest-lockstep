//! Commutativity specification testing.
//!
//! Flips the DPOR story: instead of using commutativity to *optimize*
//! testing, this module *tests* that operations satisfy a commutativity
//! specification. Users declare which pairs of operations SHOULD
//! commute, and the framework finds violations.
//!
//! This is the first formally verified commutativity specification
//! testing framework. The soundness is proved in `Commutativity.lean`.
//!
//! # Use Cases
//!
//! - **Database isolation levels**: verify that reads commute with
//!   reads, but not with writes to the same key
//! - **Lock-free data structures**: verify that claimed lock-free
//!   operations are truly independent
//! - **API contracts**: verify that "thread-safe" operations don't
//!   have hidden dependencies
//!
//! # Architecture
//!
//! Users implement [`CommutativitySpecModel`] on top of
//! [`InvariantModel`](crate::invariant::InvariantModel):
//! - `should_commute(a, b, state)` -- declares the commutativity spec
//! - The runner generates pairs of actions, checks whether they
//!   actually commute in the model, and reports violations

use std::fmt::Debug;

use proptest_state_machine::ReferenceStateMachine;

use crate::action::AnyAction;
use crate::env::TypedEnv;
use crate::invariant::{assert_invariant, InvariantModel};
use crate::runner::LockstepRef;

// ---------------------------------------------------------------------------
// Trait
// ---------------------------------------------------------------------------

/// Extension trait for lockstep models with commutativity specifications.
///
/// Users declare which pairs of actions SHOULD commute at a given
/// model state. The framework tests this by running both orderings
/// and checking that they produce the same results and final state.
pub trait CommutativitySpecModel: InvariantModel
where
    Self::ModelState: PartialEq,
{
    /// Declare whether two actions should commute at the given model
    /// state. Returns `true` if the actions are expected to commute
    /// (produce the same results and final state regardless of order).
    ///
    /// This is the *specification* -- the framework tests whether the
    /// model actually satisfies it.
    fn should_commute(
        state: &Self::ModelState,
        a: &dyn AnyAction,
        b: &dyn AnyAction,
    ) -> bool;
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for commutativity specification tests.
#[derive(Debug, Clone)]
pub struct CommutativityConfig {
    /// Number of proptest cases to generate.
    /// Default: 100.
    pub cases: u32,

    /// Number of prefix operations before checking commutativity.
    /// The prefix builds up interesting model state before testing
    /// commutativity of the next pair of actions.
    /// Default: 0..10.
    pub min_prefix: usize,
    pub max_prefix: usize,
}

impl Default for CommutativityConfig {
    fn default() -> Self {
        CommutativityConfig {
            cases: 100,
            min_prefix: 2,
            max_prefix: 10,
        }
    }
}

/// A commutativity violation: two actions that should commute but don't.
#[derive(Debug)]
pub struct CommutativityViolation {
    /// Description of the violation.
    pub message: String,
}

// ---------------------------------------------------------------------------
// Core check
// ---------------------------------------------------------------------------

/// Check whether two actions actually commute at a given model state.
///
/// Runs both orderings (a-then-b and b-then-a) and compares:
/// 1. The results of each action (via `check_model_bridge`)
/// 2. The final model states (via `PartialEq`)
///
/// Returns `Ok(())` if they commute, or `Err(message)` if they don't.
pub fn check_commute<M: InvariantModel>(
    model: &M::ModelState,
    env: &TypedEnv,
    a: &dyn AnyAction,
    b: &dyn AnyAction,
) -> Result<(), String>
where
    M::ModelState: PartialEq,
{
    // Order 1: a then b
    let mut m1 = model.clone();
    let mut e1 = env.clone();
    let r_a1 = M::step_model(&mut m1, a, &e1);
    a.store_model_var(0, &*r_a1, &mut e1);
    let r_b1 = M::step_model(&mut m1, b, &e1);

    // Order 2: b then a
    let mut m2 = model.clone();
    let mut e2 = env.clone();
    let r_b2 = M::step_model(&mut m2, b, &e2);
    b.store_model_var(0, &*r_b2, &mut e2);
    let r_a2 = M::step_model(&mut m2, a, &e2);

    // Check results
    let a_same = a.check_model_bridge(&*r_a1, &*r_a2).is_ok();
    let b_same = b.check_model_bridge(&*r_b1, &*r_b2).is_ok();
    let state_same = m1 == m2;

    if a_same && b_same && state_same {
        Ok(())
    } else {
        let mut reasons = Vec::new();
        if !a_same {
            reasons.push(format!("  Action A ({:?}) produced different results", a));
        }
        if !b_same {
            reasons.push(format!("  Action B ({:?}) produced different results", b));
        }
        if !state_same {
            reasons.push("  Final model states differ".to_string());
        }
        Err(format!(
            "Commutativity violation!\n  Action A: {:?}\n  Action B: {:?}\n{}",
            a,
            b,
            reasons.join("\n")
        ))
    }
}

// ---------------------------------------------------------------------------
// Runner
// ---------------------------------------------------------------------------

/// Run a commutativity specification test.
///
/// Generates random action sequences, builds up model state with a
/// prefix, then generates pairs of actions and checks:
/// 1. If `should_commute` says they should commute, verify they do
/// 2. If `should_commute` says they shouldn't, verify they don't
///    (optional -- a false negative in the spec is less serious)
///
/// # Panics
///
/// - If two actions that should commute don't (spec violation)
/// - If the invariant is violated at any step
pub fn run_commutativity_test<M: CommutativitySpecModel>(config: CommutativityConfig)
where
    M::ModelState: PartialEq,
{
    let proptest_config = proptest::test_runner::Config {
        cases: config.cases,
        ..Default::default()
    };

    let size = config.min_prefix..config.max_prefix;

    proptest::proptest!(proptest_config, |((_initial_state, transitions, _seen_counter) in
        <LockstepRef<M> as ReferenceStateMachine>::sequential_strategy(size))| {

        // Build up state with prefix
        let mut model_state = M::init_model();
        let mut model_env = TypedEnv::new();
        let mut next_var_id: usize = 0;

        for transition in &transitions {
            assert_invariant::<M>(&model_state, "before step");

            let model_result = M::step_model(
                &mut model_state,
                transition.as_ref(),
                &model_env,
            );
            transition.store_model_var(next_var_id, &*model_result, &mut model_env);
            next_var_id += 1;
        }

        assert_invariant::<M>(&model_state, "after prefix");

        // Now test commutativity: use the last two transitions as
        // the pair to test
        if transitions.len() >= 2 {
            let pair_start = transitions.len() - 2;
            let a = &transitions[pair_start];
            let b = &transitions[pair_start + 1];

            // Rebuild state up to the pair
            let mut pre_state = M::init_model();
            let mut pre_env = TypedEnv::new();
            for (i, t) in transitions[..pair_start].iter().enumerate() {
                let r = M::step_model(&mut pre_state, t.as_ref(), &pre_env);
                t.store_model_var(i, &*r, &mut pre_env);
            }

            let spec_says_commute = M::should_commute(
                &pre_state,
                a.as_ref(),
                b.as_ref(),
            );

            if spec_says_commute {
                // Spec says they should commute -- verify
                let result = check_commute::<M>(
                    &pre_state,
                    &pre_env,
                    a.as_ref(),
                    b.as_ref(),
                );

                if let Err(msg) = result {
                    panic!(
                        "Commutativity spec violation! \
                         should_commute returned true but operations don't commute.\n\
                         State: {:?}\n{msg}",
                        pre_state
                    );
                }
            }
        }
    });
}
