//! # proptest-lockstep
//!
//! Lockstep-style stateful property testing for Rust with 248
//! machine-checked Lean 4 theorems.
//!
//! ## Quick Example
//!
//! ```rust
//! use std::any::Any;
//! use std::collections::HashMap;
//! use proptest::prelude::*;
//! use proptest::strategy::BoxedStrategy;
//! use proptest_lockstep::prelude::*;
//!
//! // Define your model
//! #[derive(Debug, Clone, PartialEq)]
//! struct KvModel { data: HashMap<String, String> }
//!
//! // Define actions with auto-derived bridges
//! #[proptest_lockstep::lockstep_actions(state = KvModel)]
//! pub mod kv {
//!     #[action(real_return = "Option<String>")]
//!     pub struct Put { pub key: String, pub value: String }
//!
//!     #[action(real_return = "Option<String>")]
//!     pub struct Get { pub key: String }
//! }
//!
//! // Implement interpreters
//! #[derive(Debug, Clone)]
//! struct KvTest;
//!
//! impl kv::KvModelInterp for KvTest {
//!     type State = KvModel;
//!     fn put(s: &mut KvModel, a: &kv::Put, _: &TypedEnv) -> Option<String> {
//!         s.data.insert(a.key.clone(), a.value.clone())
//!     }
//!     fn get(s: &mut KvModel, a: &kv::Get, _: &TypedEnv) -> Option<String> {
//!         s.data.get(&a.key).cloned()
//!     }
//! }
//!
//! impl kv::KvSutInterp for KvTest {
//!     type Sut = HashMap<String, String>;
//!     fn put(s: &mut HashMap<String, String>, a: &kv::Put, _: &TypedEnv) -> Option<String> {
//!         s.insert(a.key.clone(), a.value.clone())
//!     }
//!     fn get(s: &mut HashMap<String, String>, a: &kv::Get, _: &TypedEnv) -> Option<String> {
//!         s.get(&a.key).cloned()
//!     }
//! }
//!
//! impl LockstepModel for KvTest {
//!     type ModelState = KvModel;
//!     type Sut = HashMap<String, String>;
//!     fn init_model() -> KvModel { KvModel { data: HashMap::new() } }
//!     fn init_sut() -> HashMap<String, String> { HashMap::new() }
//!     fn gen_action(_: &KvModel, _: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
//!         let ks = proptest::sample::select(vec!["a", "b"]).prop_map(|s| s.to_string());
//!         let vs = proptest::sample::select(vec!["1", "2"]).prop_map(|s| s.to_string());
//!         prop_oneof![
//!             (ks.clone(), vs).prop_map(|(k, v)| kv::put(kv::Put { key: k, value: v })),
//!             ks.prop_map(|k| kv::get(kv::Get { key: k })),
//!         ].boxed()
//!     }
//!     fn step_model(s: &mut KvModel, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
//!         kv::dispatch_model::<KvTest>(s, a, e)
//!     }
//!     fn step_sut(s: &mut HashMap<String, String>, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
//!         kv::dispatch_sut::<KvTest>(s, a, e)
//!     }
//! }
//!
//! // Run the test
//! run_lockstep_test::<KvTest>(1..10);
//! ```

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
pub mod certified;
pub mod classify;
pub mod commutativity;
pub mod compositional;
pub mod crash_recovery;
pub mod differential;
pub mod effects;
pub mod eventual;
pub mod depth;
pub mod regression;
pub mod session;
pub mod shrinking;
pub mod tensor;

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
    pub use crate::runner::{run_lockstep_test, run_lockstep_test_with_config, run_lockstep_test_verbose, LockstepRef, LockstepSut};
    pub use crate::witness::Is;
}

#[cfg(feature = "derive")]
pub use proptest_lockstep_derive::lockstep_actions;

// Re-export proptest and proptest-state-machine for convenience
pub use proptest;
pub use proptest_state_machine;
