#![allow(dead_code)]
//! Session consistency test for a multi-session key-value store.
//!
//! Tests that a KV store satisfies read-your-writes: if session A
//! writes a value, session A's next read sees that value.
//!
//! Run with: `cargo test --example session_kv`

use std::any::Any;
use std::collections::HashMap;

use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;
use proptest_lockstep::invariant::InvariantModel;
use proptest_lockstep::session::{SessionConsistencyModel, SessionConsistencyConfig, SessionGuarantee};

// ============================================================================
// Multi-session KV store -- SUT
// ============================================================================

/// A KV store where writes are immediately visible (satisfies
/// read-your-writes). Each operation is tagged with a session ID.
#[derive(Debug)]
struct SessionKvStore {
    data: HashMap<String, String>,
}

impl SessionKvStore {
    fn new() -> Self { SessionKvStore { data: HashMap::new() } }
    fn put(&mut self, key: &str, value: &str) { self.data.insert(key.into(), value.into()); }
    fn get(&self, key: &str) -> Option<String> { self.data.get(key).cloned() }
}

// ============================================================================
// Model
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
struct KvModel {
    data: HashMap<String, String>,
}

// ============================================================================
// Actions -- tagged with session ID
// ============================================================================

#[proptest_lockstep::lockstep_actions(state = KvModel)]
pub mod skv {
    #[action(real_return = "()")]
    pub struct Put {
        pub session: u8,
        pub key: String,
        pub value: String,
    }

    #[action(real_return = "Option<String>")]
    pub struct Get {
        pub session: u8,
        pub key: String,
    }
}

// ============================================================================
// Interpreters
// ============================================================================

#[derive(Debug, Clone)]
struct SessionKvLockstep;

impl skv::SkvModelInterp for SessionKvLockstep {
    type State = KvModel;
    fn put(s: &mut KvModel, a: &skv::Put, _: &TypedEnv) {
        s.data.insert(a.key.clone(), a.value.clone());
    }
    fn get(s: &mut KvModel, a: &skv::Get, _: &TypedEnv) -> Option<String> {
        s.data.get(&a.key).cloned()
    }
}

impl skv::SkvSutInterp for SessionKvLockstep {
    type Sut = SessionKvStore;
    fn put(s: &mut SessionKvStore, a: &skv::Put, _: &TypedEnv) {
        s.put(&a.key, &a.value);
    }
    fn get(s: &mut SessionKvStore, a: &skv::Get, _: &TypedEnv) -> Option<String> {
        s.get(&a.key)
    }
}

impl LockstepModel for SessionKvLockstep {
    type ModelState = KvModel;
    type Sut = SessionKvStore;
    fn init_model() -> KvModel { KvModel { data: HashMap::new() } }
    fn init_sut() -> SessionKvStore { SessionKvStore::new() }
    fn gen_action(_: &KvModel, _: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        let sessions = vec![0u8, 1, 2];
        let keys = vec!["x", "y"];
        let vals = vec!["a", "b", "c"];
        let ss = proptest::sample::select(sessions.clone());
        let ss2 = proptest::sample::select(sessions);
        let ks = proptest::sample::select(keys.clone()).prop_map(|s| s.to_string());
        let ks2 = proptest::sample::select(keys).prop_map(|s| s.to_string());
        let vs = proptest::sample::select(vals).prop_map(|s| s.to_string());
        prop_oneof![
            3 => (ss, ks, vs).prop_map(|(s, k, v)| skv::put(skv::Put { session: s, key: k, value: v })),
            3 => (ss2, ks2).prop_map(|(s, k)| skv::get(skv::Get { session: s, key: k })),
        ].boxed()
    }
    fn step_model(s: &mut KvModel, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        skv::dispatch_model::<SessionKvLockstep>(s, a, e)
    }
    fn step_sut(s: &mut SessionKvStore, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        skv::dispatch_sut::<SessionKvLockstep>(s, a, e)
    }
}

impl InvariantModel for SessionKvLockstep {}

// ============================================================================
// SessionConsistencyModel
// ============================================================================

impl SessionConsistencyModel for SessionKvLockstep {
    type SessionId = u8;
    type Key = String;
    type Observation = String;

    fn session_of(action: &dyn AnyAction) -> Option<u8> {
        let a = action.as_any().downcast_ref::<skv::AnySkvAction>()?;
        match a {
            skv::AnySkvAction::Put(skv::SkvGadt::Put(_, put)) => Some(put.session),
            skv::AnySkvAction::Get(skv::SkvGadt::Get(_, get)) => Some(get.session),
            _ => None,
        }
    }

    fn read_observation(
        action: &dyn AnyAction,
        result: &dyn Any,
    ) -> Option<(String, String)> {
        let a = action.as_any().downcast_ref::<skv::AnySkvAction>()?;
        match a {
            skv::AnySkvAction::Get(skv::SkvGadt::Get(_, get)) => {
                let val = result.downcast_ref::<Option<String>>()?;
                val.as_ref().map(|v| (get.key.clone(), v.clone()))
            }
            _ => None,
        }
    }

    fn write_observation(action: &dyn AnyAction) -> Option<(String, String)> {
        let a = action.as_any().downcast_ref::<skv::AnySkvAction>()?;
        match a {
            skv::AnySkvAction::Put(skv::SkvGadt::Put(_, put)) => {
                Some((put.key.clone(), put.value.clone()))
            }
            _ => None,
        }
    }

    fn guarantees() -> Vec<SessionGuarantee> {
        vec![SessionGuarantee::ReadYourWrites]
    }
}

fn main() {
    println!("Run with `cargo test --example session_kv`");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Session consistency test: verifies read-your-writes.
    /// If session A writes "x" = "a", session A's next read of "x"
    /// returns "a".
    #[test]
    fn session_kv_read_your_writes() {
        proptest_lockstep::session::run_session_consistency_test::<SessionKvLockstep>(
            SessionConsistencyConfig {
                cases: 200,
                min_ops: 5,
                max_ops: 20,
            },
        );
    }
}
