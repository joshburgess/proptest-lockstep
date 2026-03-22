#![allow(dead_code)]
//! Effect-indexed commutativity demonstration.
//!
//! Shows how static effect annotations replace the O(n²) dynamic
//! commutativity oracle with O(1) lookups. A KV store's operations
//! are annotated with read/write effects on keys, and commutativity
//! is determined from the annotations without running the model.
//!
//! Run with: `cargo test --example effect_commutativity`

use std::any::Any;
use std::collections::HashMap;

use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;
use proptest_lockstep::effects::{
    ConflictAlgebra, EffectModel, ReadWriteEffect, effects_commute,
};

// ============================================================================
// Model + Actions
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
struct KvModel { data: HashMap<String, String> }

#[proptest_lockstep::lockstep_actions(state = KvModel)]
pub mod kv {
    #[action(real_return = "Option<String>")]
    pub struct Put { pub key: String, pub value: String }

    #[action(real_return = "Option<String>")]
    pub struct Get { pub key: String }

    #[action(real_return = "usize")]
    pub struct Len;
}

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
    fn len(s: &mut KvModel, _: &kv::Len, _: &TypedEnv) -> usize {
        s.data.len()
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
    fn len(s: &mut HashMap<String, String>, _: &kv::Len, _: &TypedEnv) -> usize {
        s.len()
    }
}

impl LockstepModel for KvLockstep {
    type ModelState = KvModel;
    type Sut = HashMap<String, String>;
    fn init_model() -> KvModel { KvModel { data: HashMap::new() } }
    fn init_sut() -> HashMap<String, String> { HashMap::new() }
    fn gen_action(_: &KvModel, _: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        let keys = vec!["x", "y", "z"];
        let vals = vec!["a", "b"];
        let ks = proptest::sample::select(keys.clone()).prop_map(|s| s.to_string());
        let ks2 = proptest::sample::select(keys).prop_map(|s| s.to_string());
        let vs = proptest::sample::select(vals).prop_map(|s| s.to_string());
        prop_oneof![
            3 => (ks, vs).prop_map(|(k, v)| kv::put(kv::Put { key: k, value: v })),
            3 => ks2.prop_map(|k| kv::get(kv::Get { key: k })),
            1 => Just(kv::len(kv::Len)),
        ].boxed()
    }
    fn step_model(s: &mut KvModel, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        kv::dispatch_model::<KvLockstep>(s, a, e)
    }
    fn step_sut(s: &mut HashMap<String, String>, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        kv::dispatch_sut::<KvLockstep>(s, a, e)
    }
}

// ============================================================================
// Effect annotations
// ============================================================================

impl EffectModel for KvLockstep {
    type Effect = ReadWriteEffect<String>;

    fn effect_of(action: &dyn AnyAction) -> Option<ReadWriteEffect<String>> {
        let a = action.as_any().downcast_ref::<kv::AnyKvAction>()?;
        Some(match a {
            kv::AnyKvAction::Put(kv::KvGadt::Put(_, put)) =>
                ReadWriteEffect::Write(put.key.clone()),
            kv::AnyKvAction::Get(kv::KvGadt::Get(_, get)) =>
                ReadWriteEffect::Read(get.key.clone()),
            kv::AnyKvAction::Len(_) =>
                ReadWriteEffect::ReadAll,
            _ => ReadWriteEffect::None,
        })
    }
}

fn main() {
    println!("Run with `cargo test --example effect_commutativity`");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Two Gets always commute (Read/Read, no conflict).
    #[test]
    fn get_get_commutes() {
        let a = kv::get(kv::Get { key: "x".into() });
        let b = kv::get(kv::Get { key: "y".into() });
        assert_eq!(
            effects_commute::<KvLockstep>(a.as_ref(), b.as_ref()),
            Some(true),
        );
    }

    /// Get and Put on DIFFERENT keys commute.
    #[test]
    fn get_put_different_keys_commutes() {
        let a = kv::get(kv::Get { key: "x".into() });
        let b = kv::put(kv::Put { key: "y".into(), value: "v".into() });
        assert_eq!(
            effects_commute::<KvLockstep>(a.as_ref(), b.as_ref()),
            Some(true),
        );
    }

    /// Get and Put on SAME key don't commute.
    #[test]
    fn get_put_same_key_conflicts() {
        let a = kv::get(kv::Get { key: "x".into() });
        let b = kv::put(kv::Put { key: "x".into(), value: "v".into() });
        assert_eq!(
            effects_commute::<KvLockstep>(a.as_ref(), b.as_ref()),
            Some(false),
        );
    }

    /// Two Puts on DIFFERENT keys commute.
    #[test]
    fn put_put_different_keys_commutes() {
        let a = kv::put(kv::Put { key: "x".into(), value: "a".into() });
        let b = kv::put(kv::Put { key: "y".into(), value: "b".into() });
        assert_eq!(
            effects_commute::<KvLockstep>(a.as_ref(), b.as_ref()),
            Some(true),
        );
    }

    /// Two Puts on SAME key don't commute.
    #[test]
    fn put_put_same_key_conflicts() {
        let a = kv::put(kv::Put { key: "x".into(), value: "a".into() });
        let b = kv::put(kv::Put { key: "x".into(), value: "b".into() });
        assert_eq!(
            effects_commute::<KvLockstep>(a.as_ref(), b.as_ref()),
            Some(false),
        );
    }

    /// Len (ReadAll) commutes with Get (Read) but not with Put (Write).
    #[test]
    fn len_commutes_with_get_not_put() {
        let len = kv::len(kv::Len);
        let get = kv::get(kv::Get { key: "x".into() });
        let put = kv::put(kv::Put { key: "x".into(), value: "v".into() });

        assert_eq!(
            effects_commute::<KvLockstep>(len.as_ref(), get.as_ref()),
            Some(true),
            "Len(ReadAll) commutes with Get(Read)"
        );
        assert_eq!(
            effects_commute::<KvLockstep>(len.as_ref(), put.as_ref()),
            Some(false),
            "Len(ReadAll) conflicts with Put(Write)"
        );
    }
}
