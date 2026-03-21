//! Async support for lockstep testing.
//!
//! This module provides the `AsyncLockstepModel` trait for testing
//! async systems-under-test (e.g., async database clients, HTTP services).
//! The model remains synchronous (it's a pure data structure), but the
//! SUT execution is async.
//!
//! Requires the `async` feature flag: `proptest-lockstep = { features = ["async"] }`.

use std::any::Any;
use std::fmt::Debug;

use crate::action::AnyAction;
use crate::env::TypedEnv;
use crate::model::LockstepModel;

/// Extension trait for lockstep models with async SUTs.
///
/// The model-side operations remain synchronous (models are pure).
/// Only the SUT initialization and step are async.
///
/// # Example
///
/// ```ignore
/// use proptest_lockstep::async_support::AsyncLockstepModel;
///
/// #[derive(Debug, Clone)]
/// struct DbLockstep;
///
/// impl LockstepModel for DbLockstep {
///     type ModelState = MockDb;
///     type Sut = AsyncDbClient;
///     // ... sync model methods ...
/// }
///
/// impl AsyncLockstepModel for DbLockstep {
///     async fn init_sut_async() -> AsyncDbClient {
///         AsyncDbClient::connect("localhost:5432").await.unwrap()
///     }
///
///     async fn step_sut_async(
///         sut: &mut AsyncDbClient,
///         action: &dyn AnyAction,
///         env: &TypedEnv,
///     ) -> Box<dyn Any> {
///         // dispatch to async API
///     }
/// }
///
/// #[tokio::test]
/// async fn test_db() {
///     lockstep_test_async::<DbLockstep>(1..50).await;
/// }
/// ```
#[cfg(feature = "async")]
#[async_trait::async_trait]
pub trait AsyncLockstepModel: LockstepModel
where
    Self::Sut: Send,
{
    /// Create the initial SUT instance asynchronously.
    ///
    /// Override this when the SUT requires async initialization
    /// (e.g., establishing a database connection). The default
    /// implementation calls the sync `init_sut()`.
    async fn init_sut_async() -> Self::Sut {
        Self::init_sut()
    }

    /// Execute an action against the SUT asynchronously.
    async fn step_sut_async(
        sut: &mut Self::Sut,
        action: &dyn AnyAction,
        env: &TypedEnv,
    ) -> Box<dyn Any>;

    /// Optional async teardown for the SUT.
    async fn teardown_async(_sut: Self::Sut) {}
}

/// Run an async lockstep test.
///
/// This function generates random action sequences, executes the model
/// synchronously and the SUT asynchronously, and checks that they agree
/// at every step.
///
/// **Limitation:** Unlike the synchronous `run_lockstep_test`, this function
/// does not shrink failing sequences. When a mismatch is found, the full
/// action sequence is reported without minimization. This is because the
/// async path bypasses `proptest-state-machine`'s built-in shrinking.
///
/// Must be called from within an async runtime (e.g., `#[tokio::test]`).
///
/// # Example
///
/// ```ignore
/// #[tokio::test]
/// async fn test_async_db() {
///     lockstep_test_async::<DbModel>(1..50).await;
/// }
/// ```
#[cfg(feature = "async")]
pub async fn lockstep_test_async<M>(
    size: impl Into<proptest::collection::SizeRange>,
) where
    M: AsyncLockstepModel + Send + Sync,
    M::ModelState: Send,
    M::Sut: Send,
{
    use proptest::prelude::*;
    use proptest::strategy::ValueTree;
    use proptest::test_runner::TestRunner;

    let size_range = size.into();
    let mut runner = TestRunner::default();

    // Run multiple test cases
    for _ in 0..runner.config().cases {
        // Generate a sequence of actions
        let seq_len = {
            let (lo, hi) = (size_range.start(), size_range.end_excl());
            if lo >= hi {
                lo
            } else {
                lo + (runner.rng().next_u32() as usize % (hi - lo))
            }
        };

        let mut gen_model = M::init_model();
        let mut gen_env = TypedEnv::new();
        let mut actions: Vec<Box<dyn AnyAction>> = Vec::new();

        for _ in 0..seq_len {
            let strategy = M::gen_action(&gen_model, &gen_env);
            if let Ok(tree) = strategy.new_tree(&mut runner) {
                let action = tree.current();
                let result = M::step_model(&mut gen_model, action.as_ref(), &gen_env);
                let var_id = gen_env.next_id();
                action.store_model_var(var_id, &*result, &mut gen_env);
                actions.push(action);
            }
        }

        // Now execute: model sync, SUT async
        let mut model_state = M::init_model();
        let mut sut = M::init_sut_async().await;
        let mut model_env = TypedEnv::new();
        let mut sut_env = TypedEnv::new();

        for action in &actions {
            // Step model (sync)
            let model_result = M::step_model(&mut model_state, action.as_ref(), &model_env);

            // Step SUT (async)
            let sut_result = M::step_sut_async(&mut sut, action.as_ref(), &sut_env).await;

            // Lockstep check
            action.check_bridge(&*model_result, &*sut_result)
                .unwrap_or_else(|msg| {
                    panic!(
                        "Lockstep mismatch!\n  Action: {:?}\n{}",
                        action, msg
                    )
                });

            // Store variables
            let var_id = model_env.next_id();
            action.store_model_var(var_id, &*model_result, &mut model_env);
            action.store_sut_var(var_id, &*sut_result, &mut sut_env);
        }

        M::teardown_async(sut).await;
    }
}

