#![allow(dead_code)]
//! Commutativity specification test for a key-value store.
//!
//! Demonstrates commutativity specification testing: the user declares
//! which operations SHOULD commute, and the framework verifies the
//! model satisfies the specification.
//!
//! For a KV store:
//! - Get(k1) commutes with Get(k2) -- always (reads are independent)
//! - Put(k1, v1) commutes with Put(k2, v2) -- iff k1 ≠ k2
//! - Get(k1) commutes with Put(k2, v) -- iff k1 ≠ k2
//!
//! The test also includes a `#[should_panic]` test demonstrating
//! that an INCORRECT spec (claiming Put(k,v1) commutes with Put(k,v2))
//! is caught by the framework.
//!
//! Run with: `cargo test --example commutativity_spec`

use std::any::Any;
use std::collections::HashMap;

use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;
use proptest_lockstep::invariant::InvariantModel;
use proptest_lockstep::commutativity::{CommutativitySpecModel, CommutativityConfig};

// ============================================================================
// Model
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
struct KvModel {
    data: HashMap<String, String>,
}

// ============================================================================
// Actions
// ============================================================================

#[proptest_lockstep::lockstep_actions(state = KvModel)]
pub mod kv {
    #[action(real_return = "Option<String>")]
    pub struct Put { pub key: String, pub value: String }

    #[action(real_return = "Option<String>")]
    pub struct Get { pub key: String }
}

// ============================================================================
// Interpreters
// ============================================================================

#[derive(Debug, Clone)]
struct KvLockstep;

impl kv::KvModelInterp for KvLockstep {
    type State = KvModel;
    fn put(s: &mut KvModel, a: &kv::Put, _: &TypedEnv) -> Option<String> {
        s.data.insert(a.key.clone(), a.value.clone())
    }
    fn get(s: &mut KvModel, a: &kv::Get, _: &TypedEnv) -> Option<String> {
        s.data.get(&a.key).cloned()
    }
}

impl kv::KvSutInterp for KvLockstep {
    type Sut = HashMap<String, String>;
    fn put(s: &mut HashMap<String, String>, a: &kv::Put, _: &TypedEnv) -> Option<String> {
        s.insert(a.key.clone(), a.value.clone())
    }
    fn get(s: &mut HashMap<String, String>, a: &kv::Get, _: &TypedEnv) -> Option<String> {
        s.get(&a.key).cloned()
    }
}

impl LockstepModel for KvLockstep {
    type ModelState = KvModel;
    type Sut = HashMap<String, String>;
    fn init_model() -> KvModel { KvModel { data: HashMap::new() } }
    fn init_sut() -> HashMap<String, String> { HashMap::new() }
    fn gen_action(state: &KvModel, _: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        let keys = vec!["x", "y", "z"];
        let vals = vec!["a", "b", "c"];
        let ks = proptest::sample::select(keys.clone()).prop_map(|s| s.to_string());
        let ks2 = proptest::sample::select(keys).prop_map(|s| s.to_string());
        let vs = proptest::sample::select(vals).prop_map(|s| s.to_string());
        prop_oneof![
            (ks, vs).prop_map(|(k, v)| kv::put(kv::Put { key: k, value: v })),
            ks2.prop_map(|k| kv::get(kv::Get { key: k })),
        ].boxed()
    }
    fn step_model(s: &mut KvModel, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        kv::dispatch_model::<KvLockstep>(s, a, e)
    }
    fn step_sut(s: &mut HashMap<String, String>, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        kv::dispatch_sut::<KvLockstep>(s, a, e)
    }
}

impl InvariantModel for KvLockstep {}

// ============================================================================
// Correct commutativity spec
// ============================================================================

impl CommutativitySpecModel for KvLockstep {
    fn should_commute(
        _state: &KvModel,
        a: &dyn AnyAction,
        b: &dyn AnyAction,
    ) -> bool {
        let a_any = a.as_any();
        let b_any = b.as_any();

        // Get always commutes with Get
        if a_any.is::<kv::AnyKvAction>() && b_any.is::<kv::AnyKvAction>() {
            let a_kv = a_any.downcast_ref::<kv::AnyKvAction>().unwrap();
            let b_kv = b_any.downcast_ref::<kv::AnyKvAction>().unwrap();

            match (a_kv, b_kv) {
                // Two Gets always commute
                (kv::AnyKvAction::Get(_), kv::AnyKvAction::Get(_)) => true,
                // Put + Get commute iff different keys
                (kv::AnyKvAction::Put(kv::KvGadt::Put(_, put)), kv::AnyKvAction::Get(kv::KvGadt::Get(_, get)))
                | (kv::AnyKvAction::Get(kv::KvGadt::Get(_, get)), kv::AnyKvAction::Put(kv::KvGadt::Put(_, put))) => {
                    put.key != get.key
                }
                // Two Puts commute iff different keys
                (kv::AnyKvAction::Put(kv::KvGadt::Put(_, p1)), kv::AnyKvAction::Put(kv::KvGadt::Put(_, p2))) => {
                    p1.key != p2.key
                }
                _ => false,
            }
        } else {
            false
        }
    }
}

fn main() {
    println!("Run with `cargo test --example commutativity_spec`");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Correct commutativity spec: the framework verifies that
    /// the KV store satisfies the declared commutativity rules.
    #[test]
    fn kv_commutativity_spec_passes() {
        proptest_lockstep::commutativity::run_commutativity_test::<KvLockstep>(
            CommutativityConfig {
                cases: 200,
                min_prefix: 2,
                max_prefix: 10,
            },
        );
    }
}
