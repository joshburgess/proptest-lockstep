use std::fmt::Debug;

use proptest::strategy::BoxedStrategy;

use crate::action::AnyAction;
use crate::env::TypedEnv;

/// The main trait that users implement to define a lockstep test.
///
/// `LockstepModel` ties together:
/// - The model state type (a pure, easily-inspectable data structure).
/// - The system-under-test (SUT) type.
/// - Action generation (producing random sequences of API calls).
/// - Preconditions (filtering out invalid action sequences).
/// - Model and SUT interpreters.
///
/// Bridge checking and variable storage are handled automatically by the
/// generated `AnyAction` impl — users don't need to implement those.
///
/// For the model and SUT interpreters, use the generated `dispatch_model`
/// and `dispatch_sut` helpers with the typed interpreter traits, or
/// implement `step_model`/`step_sut` directly.
pub trait LockstepModel: Debug + Clone + 'static {
    /// The pure model state.
    type ModelState: Debug + Clone + 'static;

    /// The real system-under-test.
    type Sut: Debug + 'static;

    /// Create the initial model state.
    fn init_model() -> Self::ModelState;

    /// Create the initial SUT instance.
    fn init_sut() -> Self::Sut;

    /// Generate a random action given the current model state and
    /// variable environment.
    fn gen_action(
        state: &Self::ModelState,
        env: &TypedEnv,
    ) -> BoxedStrategy<Box<dyn AnyAction>>;

    /// Check whether an action is valid given the current model state.
    fn precondition(
        _state: &Self::ModelState,
        _action: &dyn AnyAction,
        _env: &TypedEnv,
    ) -> bool {
        true
    }

    /// Execute an action against the model, returning the result.
    ///
    /// Typical implementation using generated dispatch:
    /// ```ignore
    /// fn step_model(state: &mut MyModel, action: &dyn AnyAction, env: &TypedEnv) -> Box<dyn Any> {
    ///     my_actions::dispatch_model::<Self>(state, action, env)
    /// }
    /// ```
    fn step_model(
        state: &mut Self::ModelState,
        action: &dyn AnyAction,
        env: &TypedEnv,
    ) -> Box<dyn std::any::Any>;

    /// Execute an action against the SUT, returning the result.
    ///
    /// Typical implementation using generated dispatch:
    /// ```ignore
    /// fn step_sut(sut: &mut MySut, action: &dyn AnyAction, env: &TypedEnv) -> Box<dyn Any> {
    ///     my_actions::dispatch_sut::<Self>(sut, action, env)
    /// }
    /// ```
    fn step_sut(
        sut: &mut Self::Sut,
        action: &dyn AnyAction,
        env: &TypedEnv,
    ) -> Box<dyn std::any::Any>;
}
