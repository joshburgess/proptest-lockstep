#![allow(dead_code)]
//! DashMap lockstep test — testing a popular concurrent HashMap.
//!
//! Tests `dashmap::DashMap` (~30M downloads) against a sequential
//! `std::collections::HashMap` model. DashMap uses sharded locking
//! internally and has had historical concurrency bugs (deadlocks,
//! incorrect iteration under concurrent modification).
//!
//! This test exercises:
//! - `insert` / `get` / `remove` — core CRUD operations
//! - `contains_key` / `len` — query operations
//! - `entry` API via `or_insert` — conditional insert
//! - `alter` — in-place mutation
//!
//! Run with:
//!   `cargo test --example dashmap_test`                         (sequential)
//!   `cargo test --example dashmap_test --features concurrent`   (all tests)

use std::any::Any;
use std::collections::HashMap;

use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;

// ============================================================================
// Model — sequential HashMap
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
struct DashModel {
    data: HashMap<String, i32>,
}

impl DashModel {
    fn new() -> Self {
        DashModel {
            data: HashMap::new(),
        }
    }
}

// ============================================================================
// Actions
// ============================================================================

#[proptest_lockstep::lockstep_actions(state = DashModel)]
pub mod dm {
    // insert returns Option<V> (the previous value)
    #[action(real_return = "Option<i32>")]
    pub struct Insert {
        pub key: String,
        pub value: i32,
    }

    // get returns Option<V> (cloned)
    #[action(real_return = "Option<i32>")]
    pub struct Get {
        pub key: String,
    }

    // remove returns Option<(K, V)>, we return just the value
    #[action(real_return = "Option<i32>")]
    pub struct Remove {
        pub key: String,
    }

    #[action(real_return = "bool")]
    pub struct ContainsKey {
        pub key: String,
    }

    #[action(real_return = "usize")]
    pub struct Len;

    // entry().or_insert(val) — inserts if absent, returns the current value
    #[action(real_return = "i32")]
    pub struct GetOrInsert {
        pub key: String,
        pub default: i32,
    }

    // alter — mutate in place. We use a simple increment.
    // Returns whether the key existed.
    #[action(real_return = "bool")]
    pub struct IncrementIfExists {
        pub key: String,
    }
}

// ============================================================================
// Interpreters
// ============================================================================

#[derive(Debug, Clone)]
struct DashMapLockstep;

impl dm::DmModelInterp for DashMapLockstep {
    type State = DashModel;

    fn insert(s: &mut DashModel, a: &dm::Insert, _: &TypedEnv) -> Option<i32> {
        s.data.insert(a.key.clone(), a.value)
    }

    fn get(s: &mut DashModel, a: &dm::Get, _: &TypedEnv) -> Option<i32> {
        s.data.get(&a.key).copied()
    }

    fn remove(s: &mut DashModel, a: &dm::Remove, _: &TypedEnv) -> Option<i32> {
        s.data.remove(&a.key)
    }

    fn contains_key(s: &mut DashModel, a: &dm::ContainsKey, _: &TypedEnv) -> bool {
        s.data.contains_key(&a.key)
    }

    fn len(s: &mut DashModel, _: &dm::Len, _: &TypedEnv) -> usize {
        s.data.len()
    }

    fn get_or_insert(s: &mut DashModel, a: &dm::GetOrInsert, _: &TypedEnv) -> i32 {
        *s.data.entry(a.key.clone()).or_insert(a.default)
    }

    fn increment_if_exists(s: &mut DashModel, a: &dm::IncrementIfExists, _: &TypedEnv) -> bool {
        if let Some(v) = s.data.get_mut(&a.key) {
            *v += 1;
            true
        } else {
            false
        }
    }
}

impl dm::DmSutInterp for DashMapLockstep {
    type Sut = dashmap::DashMap<String, i32>;

    fn insert(s: &mut dashmap::DashMap<String, i32>, a: &dm::Insert, _: &TypedEnv) -> Option<i32> {
        s.insert(a.key.clone(), a.value)
    }

    fn get(s: &mut dashmap::DashMap<String, i32>, a: &dm::Get, _: &TypedEnv) -> Option<i32> {
        s.get(&a.key).map(|v| *v)
    }

    fn remove(s: &mut dashmap::DashMap<String, i32>, a: &dm::Remove, _: &TypedEnv) -> Option<i32> {
        s.remove(&a.key).map(|(_k, v)| v)
    }

    fn contains_key(
        s: &mut dashmap::DashMap<String, i32>,
        a: &dm::ContainsKey,
        _: &TypedEnv,
    ) -> bool {
        s.contains_key(&a.key)
    }

    fn len(s: &mut dashmap::DashMap<String, i32>, _: &dm::Len, _: &TypedEnv) -> usize {
        s.len()
    }

    fn get_or_insert(
        s: &mut dashmap::DashMap<String, i32>,
        a: &dm::GetOrInsert,
        _: &TypedEnv,
    ) -> i32 {
        *s.entry(a.key.clone()).or_insert(a.default)
    }

    fn increment_if_exists(
        s: &mut dashmap::DashMap<String, i32>,
        a: &dm::IncrementIfExists,
        _: &TypedEnv,
    ) -> bool {
        if let Some(mut v) = s.get_mut(&a.key) {
            *v += 1;
            true
        } else {
            false
        }
    }
}

// ============================================================================
// LockstepModel
// ============================================================================

impl LockstepModel for DashMapLockstep {
    type ModelState = DashModel;
    type Sut = dashmap::DashMap<String, i32>;

    fn init_model() -> DashModel {
        DashModel::new()
    }
    fn init_sut() -> dashmap::DashMap<String, i32> {
        dashmap::DashMap::new()
    }

    fn gen_action(state: &DashModel, _env: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        let keys: Vec<String> = state.data.keys().cloned().collect();

        let key_strat = if keys.is_empty() {
            proptest::sample::select(vec!["a", "b", "c", "d"])
                .prop_map(|s| s.to_string())
                .boxed()
        } else {
            prop_oneof![
                3 => proptest::sample::select(keys.clone()).boxed(),
                1 => proptest::sample::select(vec!["a", "b", "c", "d"])
                    .prop_map(|s| s.to_string())
                    .boxed(),
            ]
            .boxed()
        };

        let ks2 = key_strat.clone();
        let ks3 = key_strat.clone();
        let ks4 = key_strat.clone();
        let ks5 = key_strat.clone();
        let ks6 = key_strat.clone();

        prop_oneof![
            3 => (key_strat, 0i32..100).prop_map(|(k, v)| dm::insert(dm::Insert { key: k, value: v })),
            3 => ks2.prop_map(|k| dm::get(dm::Get { key: k })),
            2 => ks3.prop_map(|k| dm::remove(dm::Remove { key: k })),
            2 => ks4.prop_map(|k| dm::contains_key(dm::ContainsKey { key: k })),
            1 => Just(dm::len(dm::Len)),
            2 => (ks5, 0i32..100).prop_map(|(k, d)| dm::get_or_insert(dm::GetOrInsert { key: k, default: d })),
            2 => ks6.prop_map(|k| dm::increment_if_exists(dm::IncrementIfExists { key: k })),
        ]
        .boxed()
    }

    fn step_model(state: &mut DashModel, action: &dyn AnyAction, env: &TypedEnv) -> Box<dyn Any> {
        dm::dispatch_model::<DashMapLockstep>(state, action, env)
    }

    fn step_sut(
        sut: &mut dashmap::DashMap<String, i32>,
        action: &dyn AnyAction,
        env: &TypedEnv,
    ) -> Box<dyn Any> {
        dm::dispatch_sut::<DashMapLockstep>(sut, action, env)
    }
}

#[cfg(feature = "concurrent")]
impl proptest_lockstep::concurrent::ConcurrentLockstepModel for DashMapLockstep {
    fn step_sut_send(
        sut: &mut dashmap::DashMap<String, i32>,
        action: &dyn AnyAction,
        env: &TypedEnv,
    ) -> Box<dyn Any + Send> {
        dm::dispatch_sut_send::<DashMapLockstep>(sut, action, env)
    }
}

fn main() {
    println!("Run with `cargo test --example dashmap_test`");
    println!("  or `cargo test --example dashmap_test --features concurrent`");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Sequential lockstep: DashMap matches std::HashMap model.
    #[test]
    fn lockstep_dashmap() {
        proptest_lockstep::runner::run_lockstep_test::<DashMapLockstep>(1..50);
    }
}

#[cfg(all(test, feature = "concurrent"))]
mod concurrent_tests {
    use super::*;
    use proptest_lockstep::concurrent::{
        lockstep_concurrent, lockstep_concurrent_with_check, lockstep_linearizable,
        ConcurrentConfig, SplitStrategy,
    };

    #[test]
    fn dashmap_crash_absence() {
        lockstep_concurrent::<DashMapLockstep>(ConcurrentConfig {
            iterations: 100,
            prefix_len: 5,
            branch_len: 4,
            branch_count: 2,
            split_strategy: SplitStrategy::RoundRobin,
            ..Default::default()
        });
    }

    #[test]
    fn dashmap_final_check() {
        lockstep_concurrent_with_check::<DashMapLockstep, _>(
            ConcurrentConfig {
                iterations: 100,
                prefix_len: 3,
                branch_len: 5,
                branch_count: 2,
                split_strategy: SplitStrategy::Random { seed: 42 },
                ..Default::default()
            },
            |sut: &dashmap::DashMap<String, i32>| {
                // Verify len is consistent with iteration count
                let len = sut.len();
                let mut count = 0;
                sut.iter().for_each(|_| count += 1);
                assert_eq!(
                    len, count,
                    "DashMap len() = {} but iter counted {} entries",
                    len, count
                );
            },
        );
    }

    #[test]
    fn dashmap_linearizable() {
        lockstep_linearizable::<DashMapLockstep>(ConcurrentConfig {
            iterations: 50,
            prefix_len: 3,
            branch_len: 3,
            branch_count: 2,
            split_strategy: SplitStrategy::RoundRobin,
            ..Default::default()
        });
    }

    #[test]
    fn dashmap_conflict_maximizing() {
        lockstep_linearizable::<DashMapLockstep>(ConcurrentConfig {
            iterations: 50,
            prefix_len: 3,
            branch_len: 4,
            branch_count: 2,
            split_strategy: SplitStrategy::ConflictMaximizing,
            ..Default::default()
        });
    }
}
