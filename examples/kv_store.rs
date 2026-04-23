#![allow(dead_code)]
//! Key-value store lockstep test.
//!
//! The simplest possible lockstep test: all types are transparent (no
//! opaque handles), so `model_return` can be omitted (defaults to `real_return`).

use std::any::Any;
use std::collections::HashMap;

use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;

// ============================================================================
// System under test
// ============================================================================

#[derive(Debug)]
struct KvStore {
    data: HashMap<String, String>,
}

impl KvStore {
    fn new() -> Self { KvStore { data: HashMap::new() } }
    fn put(&mut self, key: &str, value: &str) -> Option<String> { self.data.insert(key.into(), value.into()) }
    fn get(&self, key: &str) -> Option<String> { self.data.get(key).cloned() }
    fn delete(&mut self, key: &str) -> Option<String> { self.data.remove(key) }
    fn len(&self) -> usize { self.data.len() }
}

// ============================================================================
// Model
// ============================================================================

#[derive(Debug, Clone)]
struct KvModel {
    data: HashMap<String, String>,
}

// ============================================================================
// Actions -- model_return omitted (defaults to real_return)
// ============================================================================

#[proptest_lockstep::lockstep_actions(state = KvModel)]
pub mod kv {
    #[action(real_return = "Option<String>", bridge = "OptionBridge<Transparent<String>>")]
    pub struct Put { pub key: String, pub value: String }

    #[action(real_return = "Option<String>", bridge = "OptionBridge<Transparent<String>>")]
    pub struct Get { pub key: String }

    #[action(real_return = "Option<String>", bridge = "OptionBridge<Transparent<String>>")]
    pub struct Delete { pub key: String }

    #[action(real_return = "usize", bridge = "Transparent<usize>")]
    pub struct Len;
}

// ============================================================================
// Interpreters -- typed, no downcasting, no Box<dyn Any>
// ============================================================================

#[derive(Debug, Clone)]
struct KvLockstep;

impl kv::KvModelInterp for KvLockstep {
    type State = KvModel;
    fn put(s: &mut KvModel, a: &kv::Put, _: &TypedEnv) -> Option<String> { s.data.insert(a.key.clone(), a.value.clone()) }
    fn get(s: &mut KvModel, a: &kv::Get, _: &TypedEnv) -> Option<String> { s.data.get(&a.key).cloned() }
    fn delete(s: &mut KvModel, a: &kv::Delete, _: &TypedEnv) -> Option<String> { s.data.remove(&a.key) }
    fn len(s: &mut KvModel, _: &kv::Len, _: &TypedEnv) -> usize { s.data.len() }
}

impl kv::KvSutInterp for KvLockstep {
    type Sut = KvStore;
    fn put(s: &mut KvStore, a: &kv::Put, _: &TypedEnv) -> Option<String> { s.put(&a.key, &a.value) }
    fn get(s: &mut KvStore, a: &kv::Get, _: &TypedEnv) -> Option<String> { s.get(&a.key) }
    fn delete(s: &mut KvStore, a: &kv::Delete, _: &TypedEnv) -> Option<String> { s.delete(&a.key) }
    fn len(s: &mut KvStore, _: &kv::Len, _: &TypedEnv) -> usize { s.len() }
}

// ============================================================================
// LockstepModel -- just wiring
// ============================================================================

impl LockstepModel for KvLockstep {
    type ModelState = KvModel;
    type Sut = KvStore;

    fn init_model() -> KvModel { KvModel { data: HashMap::new() } }
    fn init_sut() -> KvStore { KvStore::new() }

    fn gen_action(state: &KvModel, _env: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        let keys: Vec<String> = state.data.keys().cloned().collect();
        let key_strat = if keys.is_empty() {
            "[a-z]{1,5}".boxed()
        } else {
            prop_oneof![2 => proptest::sample::select(keys), 1 => "[a-z]{1,5}"].boxed()
        };

        let ks2 = key_strat.clone();
        let ks3 = key_strat.clone();

        prop_oneof![
            3 => (key_strat, "[a-z]{1,10}").prop_map(|(k, v)| kv::put(kv::Put { key: k, value: v })),
            3 => ks2.prop_map(|k| kv::get(kv::Get { key: k })),
            2 => ks3.prop_map(|k| kv::delete(kv::Delete { key: k })),
            1 => Just(kv::len(kv::Len)),
        ].boxed()
    }

    fn step_model(state: &mut KvModel, action: &dyn AnyAction, env: &TypedEnv) -> Box<dyn Any> {
        kv::dispatch_model::<KvLockstep>(state, action, env)
    }

    fn step_sut(sut: &mut KvStore, action: &dyn AnyAction, env: &TypedEnv) -> Box<dyn Any> {
        kv::dispatch_sut::<KvLockstep>(sut, action, env)
    }
}

fn main() {
    println!("Run with `cargo test --example kv_store`");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lockstep_kv() {
        proptest_lockstep::runner::run_lockstep_test::<KvLockstep>(1..50);
    }
}
