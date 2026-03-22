pub mod action;
pub mod bridge;
pub mod env;
pub mod gvar;
pub mod model;
pub mod op;
pub mod phase;
pub mod runner;
pub mod theory;
pub mod witness;

pub mod contracts;
pub mod coverage;
pub mod invariant;
pub mod commutativity;
pub mod crash_recovery;
pub mod differential;
pub mod effects;
pub mod eventual;
pub mod session;
pub mod shrinking;

#[cfg(feature = "concurrent")]
pub mod concurrent;

#[cfg(feature = "async")]
pub mod async_support;

/// Convenience prelude for common imports.
pub mod prelude {
    pub use crate::action::AnyAction;
    pub use crate::bridge::{
        LockstepBridge, Opaque, OptionBridge, ResultBridge, Transparent, Tuple3Bridge,
        TupleBridge, UnitBridge, VecBridge,
    };
    pub use crate::env::{TypedEnv, VarKey};
    pub use crate::gvar::{resolve_gvar, resolve_model_gvar, GVar};
    pub use crate::model::LockstepModel;
    pub use crate::op::{Op, OpComp, OpErr, OpFst, OpId, OpIndex, OpOk, OpSnd, OpSome};
    pub use crate::phase::{ConVar, Concrete, Phase, SymVar, Symbolic};
    pub use crate::runner::{run_lockstep_test, run_lockstep_test_with_config, LockstepRef, LockstepSut};
    pub use crate::witness::Is;
}

#[cfg(feature = "derive")]
pub use proptest_lockstep_derive::lockstep_actions;

// Re-export proptest and proptest-state-machine for convenience
pub use proptest;
pub use proptest_state_machine;
