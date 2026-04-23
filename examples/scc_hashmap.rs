#![allow(dead_code)]
//! scc::HashMap lockstep test -- testing a real concurrent HashMap.
//!
//! Tests `scc::HashMap` (scalable concurrent HashMap) against a
//! sequential `std::collections::HashMap` model. `scc` is a newer
//! concurrent collections crate that uses epoch-based reclamation
//! and optimistic locking, making it a good target for finding
//! potential linearizability issues.
//!
//! Run with:
//!   `cargo test --example scc_hashmap`                         (sequential)
//!   `cargo test --example scc_hashmap --features concurrent`   (all tests)

use std::any::Any;
use std::collections::HashMap;

use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;

// ============================================================================
// Model -- sequential HashMap
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
struct MapModel {
    data: HashMap<String, String>,
}

impl MapModel {
    fn new() -> Self {
        MapModel {
            data: HashMap::new(),
        }
    }
}

// ============================================================================
// Actions
// ============================================================================

#[proptest_lockstep::lockstep_actions(state = MapModel)]
pub mod hm {
    // scc::HashMap::insert returns Result<(), (K, V)> -- Err if key exists.
    // We simplify: return whether the insert succeeded.
    #[action(real_return = "bool")]
    pub struct Insert {
        pub key: String,
        pub value: String,
    }

    // scc::HashMap::upsert returns Option<V> -- the previous value.
    #[action(real_return = "Option<String>")]
    pub struct Upsert {
        pub key: String,
        pub value: String,
    }

    // scc::HashMap::remove returns Option<(K, V)>.
    // We return just the value for simplicity.
    #[action(real_return = "Option<String>")]
    pub struct Remove {
        pub key: String,
    }

    // scc::HashMap::read returns Option<R> via a reader closure.
    #[action(real_return = "Option<String>")]
    pub struct Read {
        pub key: String,
    }

    // scc::HashMap::contains returns bool.
    #[action(real_return = "bool")]
    pub struct Contains {
        pub key: String,
    }

    // scc::HashMap::len returns usize.
    #[action(real_return = "usize")]
    pub struct Len;
}

// ============================================================================
// Interpreters
// ============================================================================

#[derive(Debug, Clone)]
struct SccMapLockstep;

impl hm::HmModelInterp for SccMapLockstep {
    type State = MapModel;

    fn insert(s: &mut MapModel, a: &hm::Insert, _: &TypedEnv) -> bool {
        if s.data.contains_key(&a.key) {
            false
        } else {
            s.data.insert(a.key.clone(), a.value.clone());
            true
        }
    }

    fn upsert(s: &mut MapModel, a: &hm::Upsert, _: &TypedEnv) -> Option<String> {
        s.data.insert(a.key.clone(), a.value.clone())
    }

    fn remove(s: &mut MapModel, a: &hm::Remove, _: &TypedEnv) -> Option<String> {
        s.data.remove(&a.key)
    }

    fn read(s: &mut MapModel, a: &hm::Read, _: &TypedEnv) -> Option<String> {
        s.data.get(&a.key).cloned()
    }

    fn contains(s: &mut MapModel, a: &hm::Contains, _: &TypedEnv) -> bool {
        s.data.contains_key(&a.key)
    }

    fn len(s: &mut MapModel, _: &hm::Len, _: &TypedEnv) -> usize {
        s.data.len()
    }
}

impl hm::HmSutInterp for SccMapLockstep {
    type Sut = scc::HashMap<String, String>;

    fn insert(s: &mut scc::HashMap<String, String>, a: &hm::Insert, _: &TypedEnv) -> bool {
        s.insert(a.key.clone(), a.value.clone()).is_ok()
    }

    fn upsert(s: &mut scc::HashMap<String, String>, a: &hm::Upsert, _: &TypedEnv) -> Option<String> {
        s.upsert(a.key.clone(), a.value.clone())
    }

    fn remove(s: &mut scc::HashMap<String, String>, a: &hm::Remove, _: &TypedEnv) -> Option<String> {
        s.remove(&a.key).map(|(_k, v)| v)
    }

    fn read(s: &mut scc::HashMap<String, String>, a: &hm::Read, _: &TypedEnv) -> Option<String> {
        s.read(&a.key, |_k, v| v.clone())
    }

    fn contains(s: &mut scc::HashMap<String, String>, a: &hm::Contains, _: &TypedEnv) -> bool {
        s.contains(&a.key)
    }

    fn len(s: &mut scc::HashMap<String, String>, _: &hm::Len, _: &TypedEnv) -> usize {
        s.len()
    }
}

// ============================================================================
// LockstepModel
// ============================================================================

impl LockstepModel for SccMapLockstep {
    type ModelState = MapModel;
    type Sut = scc::HashMap<String, String>;

    fn init_model() -> MapModel {
        MapModel::new()
    }
    fn init_sut() -> scc::HashMap<String, String> {
        scc::HashMap::new()
    }

    fn gen_action(state: &MapModel, _env: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        let keys: Vec<String> = state.data.keys().cloned().collect();

        let key_strat = if keys.is_empty() {
            proptest::sample::select(vec!["a", "b", "c", "d", "e"])
                .prop_map(|s| s.to_string())
                .boxed()
        } else {
            prop_oneof![
                3 => proptest::sample::select(keys.clone()).boxed(),
                1 => proptest::sample::select(vec!["a", "b", "c", "d", "e"])
                    .prop_map(|s| s.to_string())
                    .boxed(),
            ]
            .boxed()
        };

        let ks2 = key_strat.clone();
        let ks3 = key_strat.clone();
        let ks4 = key_strat.clone();
        let ks5 = key_strat.clone();

        let val_strat = proptest::sample::select(vec!["v1", "v2", "v3", "v4"])
            .prop_map(|s| s.to_string());
        let val_strat2 = proptest::sample::select(vec!["v1", "v2", "v3", "v4"])
            .prop_map(|s| s.to_string());

        prop_oneof![
            3 => (key_strat, val_strat).prop_map(|(k, v)| hm::insert(hm::Insert { key: k, value: v })),
            3 => (ks2, val_strat2).prop_map(|(k, v)| hm::upsert(hm::Upsert { key: k, value: v })),
            3 => ks3.prop_map(|k| hm::read(hm::Read { key: k })),
            2 => ks4.prop_map(|k| hm::remove(hm::Remove { key: k })),
            2 => ks5.prop_map(|k| hm::contains(hm::Contains { key: k })),
            1 => Just(hm::len(hm::Len)),
        ]
        .boxed()
    }

    fn step_model(state: &mut MapModel, action: &dyn AnyAction, env: &TypedEnv) -> Box<dyn Any> {
        hm::dispatch_model::<SccMapLockstep>(state, action, env)
    }

    fn step_sut(
        sut: &mut scc::HashMap<String, String>,
        action: &dyn AnyAction,
        env: &TypedEnv,
    ) -> Box<dyn Any> {
        hm::dispatch_sut::<SccMapLockstep>(sut, action, env)
    }
}

#[cfg(feature = "concurrent")]
impl proptest_lockstep::concurrent::ConcurrentLockstepModel for SccMapLockstep {
    fn step_sut_send(
        sut: &mut scc::HashMap<String, String>,
        action: &dyn AnyAction,
        env: &TypedEnv,
    ) -> Box<dyn Any + Send> {
        hm::dispatch_sut_send::<SccMapLockstep>(sut, action, env)
    }
}

fn main() {
    println!("Run with `cargo test --example scc_hashmap`");
    println!("  or `cargo test --example scc_hashmap --features concurrent`");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Sequential lockstep: scc::HashMap matches std::HashMap model.
    #[test]
    fn lockstep_scc_hashmap() {
        proptest_lockstep::runner::run_lockstep_test::<SccMapLockstep>(1..50);
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
    fn scc_hashmap_crash_absence() {
        lockstep_concurrent::<SccMapLockstep>(ConcurrentConfig {
            iterations: 100,
            prefix_len: 5,
            branch_len: 4,
            branch_count: 2,
            split_strategy: SplitStrategy::RoundRobin,
            ..Default::default()
        });
    }

    #[test]
    fn scc_hashmap_final_check() {
        lockstep_concurrent_with_check::<SccMapLockstep, _>(
            ConcurrentConfig {
                iterations: 100,
                prefix_len: 3,
                branch_len: 5,
                branch_count: 2,
                split_strategy: SplitStrategy::Random { seed: 42 },
                ..Default::default()
            },
            |sut: &scc::HashMap<String, String>| {
                // Length should be non-negative (trivially true for usize)
                // and consistent with entries
                let len = sut.len();
                let mut count = 0;
                sut.scan(|_k, _v| count += 1);
                assert_eq!(
                    len, count,
                    "len() = {} but scan counted {} entries",
                    len, count
                );
            },
        );
    }

    #[test]
    fn scc_hashmap_linearizable() {
        lockstep_linearizable::<SccMapLockstep>(ConcurrentConfig {
            iterations: 50,
            prefix_len: 3,
            branch_len: 3,
            branch_count: 2,
            split_strategy: SplitStrategy::RoundRobin,
            ..Default::default()
        });
    }

    #[test]
    fn scc_hashmap_conflict_maximizing() {
        lockstep_linearizable::<SccMapLockstep>(ConcurrentConfig {
            iterations: 50,
            prefix_len: 3,
            branch_len: 4,
            branch_count: 2,
            split_strategy: SplitStrategy::ConflictMaximizing,
            ..Default::default()
        });
    }
}
