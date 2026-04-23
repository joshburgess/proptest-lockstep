use std::any::Any;
use std::fmt::Debug;

use dyn_clone::DynClone;

use crate::env::TypedEnv;

/// Trait object interface for actions with erased return types.
///
/// This is the existential boundary -- the only dynamic dispatch point in the
/// system. All typed logic (model execution, SUT execution, bridge comparison,
/// variable projection) is fully monomorphized inside each GADT variant.
/// `Box<dyn AnyAction>` exists only at the sequence container boundary,
/// exactly where Haskell uses `Any (LockstepAction state)`.
///
/// The `#[lockstep_actions]` proc macro generates a concrete enum that
/// implements this trait for each action module.
pub trait AnyAction: Debug + DynClone + Send {
    /// Upcast to `&dyn Any` for downcasting to concrete action types.
    fn as_any(&self) -> &dyn Any;

    /// Returns the IDs of symbolic variables that this action references.
    /// Used for precondition checking during shrinking -- if a depended-upon
    /// action is removed, this action must be removed too.
    fn used_vars(&self) -> Vec<usize>;

    /// Compare model and SUT results through the appropriate bridge.
    /// Returns `Ok(())` on match, or an error message describing the mismatch.
    fn check_bridge(&self, model_result: &dyn Any, sut_result: &dyn Any) -> Result<(), String>;

    /// Compare two model results through the bridge, using `observe_model`
    /// on both sides. Used by DPOR commutativity checks where both values
    /// are model results.
    ///
    /// Default: falls back to `check_bridge` (correct for symmetric bridges
    /// where `observe_real == observe_model`).
    fn check_model_bridge(&self, m1: &dyn Any, m2: &dyn Any) -> Result<(), String> {
        self.check_bridge(m1, m2)
    }

    /// Store the model result as a new variable in the model environment.
    /// The variable ID is allocated by the runner and passed in.
    fn store_model_var(&self, var_id: usize, result: &dyn Any, env: &mut TypedEnv);

    /// Store the SUT result as a new variable in the real environment.
    fn store_sut_var(&self, var_id: usize, result: &dyn Any, env: &mut TypedEnv);
}

dyn_clone::clone_trait_object!(AnyAction);
