#![allow(dead_code)]
//! LRU cache lockstep test.
//!
//! Tests an LRU (least-recently-used) cache against a sequential model.
//! The cache has a fixed capacity and evicts the least-recently-used
//! entry when full. This is the most complex case study — it involves
//! capacity management, ordering invariants, and state-dependent
//! eviction behavior.
//!
//! Demonstrates:
//! - **Eviction semantics**: automatic eviction of LRU entries on insert
//! - **Access-order tracking**: `get` promotes entries to most-recent
//! - **Rich state interactions**: capacity, ordering, and presence
//!   interact in non-trivial ways
//! - **Auto-derived bridges**: all bridges derived from return types
//! - **Concurrent linearizability**: concurrent get/put is linearizable
//!
//! Run with:
//!   `cargo test --example lru_cache`                         (sequential)
//!   `cargo test --example lru_cache --features concurrent`   (all tests)

use std::any::Any;
use std::collections::{HashMap, VecDeque};
use std::sync::Mutex;

use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;

// ============================================================================
// LRU Cache — SUT
// ============================================================================

/// A simple LRU cache backed by a HashMap + VecDeque for ordering.
///
/// On `put`, if the cache is at capacity, the least-recently-used
/// entry is evicted. On `get`, the accessed entry is promoted to
/// most-recently-used.
pub struct LruCache {
    map: HashMap<String, String>,
    order: VecDeque<String>,
    capacity: usize,
}

impl LruCache {
    fn new(capacity: usize) -> Self {
        LruCache {
            map: HashMap::new(),
            order: VecDeque::with_capacity(capacity),
            capacity,
        }
    }

    fn get(&mut self, key: &str) -> Option<String> {
        if self.map.contains_key(key) {
            // Promote to most-recently-used
            self.order.retain(|k| k != key);
            self.order.push_back(key.to_string());
            self.map.get(key).cloned()
        } else {
            None
        }
    }

    fn put(&mut self, key: &str, value: &str) -> Option<String> {
        // If key exists, update and promote
        if self.map.contains_key(key) {
            self.order.retain(|k| k != key);
            self.order.push_back(key.to_string());
            return self.map.insert(key.into(), value.into());
        }

        // If at capacity, evict LRU
        if self.map.len() >= self.capacity {
            if let Some(evicted_key) = self.order.pop_front() {
                self.map.remove(&evicted_key);
            }
        }

        self.order.push_back(key.to_string());
        self.map.insert(key.into(), value.into())
    }

    fn remove(&mut self, key: &str) -> Option<String> {
        self.order.retain(|k| k != key);
        self.map.remove(key)
    }

    fn contains(&self, key: &str) -> bool {
        self.map.contains_key(key)
    }

    fn len(&self) -> usize {
        self.map.len()
    }
}

impl std::fmt::Debug for LruCache {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LruCache")
            .field("capacity", &self.capacity)
            .field("len", &self.map.len())
            .field("order", &self.order)
            .finish()
    }
}

// ============================================================================
// Model — sequential LRU cache
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
struct LruModel {
    map: HashMap<String, String>,
    order: VecDeque<String>,
    capacity: usize,
}

impl LruModel {
    fn new(capacity: usize) -> Self {
        LruModel {
            map: HashMap::new(),
            order: VecDeque::with_capacity(capacity),
            capacity,
        }
    }

    fn get(&mut self, key: &str) -> Option<String> {
        if self.map.contains_key(key) {
            self.order.retain(|k| k != key);
            self.order.push_back(key.to_string());
            self.map.get(key).cloned()
        } else {
            None
        }
    }

    fn put(&mut self, key: &str, value: &str) -> Option<String> {
        if self.map.contains_key(key) {
            self.order.retain(|k| k != key);
            self.order.push_back(key.to_string());
            return self.map.insert(key.into(), value.into());
        }

        if self.map.len() >= self.capacity {
            if let Some(evicted_key) = self.order.pop_front() {
                self.map.remove(&evicted_key);
            }
        }

        self.order.push_back(key.to_string());
        self.map.insert(key.into(), value.into())
    }

    fn remove(&mut self, key: &str) -> Option<String> {
        self.order.retain(|k| k != key);
        self.map.remove(key)
    }

    fn contains(&self, key: &str) -> bool {
        self.map.contains_key(key)
    }

    fn len(&self) -> usize {
        self.map.len()
    }
}

// ============================================================================
// Actions — with auto-derived bridges
// ============================================================================

#[proptest_lockstep::lockstep_actions(state = LruModel)]
pub mod lru {
    // Bridge: OptionBridge<Transparent<String>>
    #[action(real_return = "Option<String>")]
    pub struct Get {
        pub key: String,
    }

    // Returns the previous value if key existed.
    // Bridge: OptionBridge<Transparent<String>>
    #[action(real_return = "Option<String>")]
    pub struct Put {
        pub key: String,
        pub value: String,
    }

    // Bridge: OptionBridge<Transparent<String>>
    #[action(real_return = "Option<String>")]
    pub struct Remove {
        pub key: String,
    }

    // Bridge: Transparent<bool>
    #[action(real_return = "bool")]
    pub struct Contains {
        pub key: String,
    }

    // Bridge: Transparent<usize>
    #[action(real_return = "usize")]
    pub struct Len;
}

// ============================================================================
// Interpreters
// ============================================================================

#[derive(Debug, Clone)]
struct LruLockstep;

const LRU_CAPACITY: usize = 3;

impl lru::LruModelInterp for LruLockstep {
    type State = LruModel;

    fn get(s: &mut LruModel, a: &lru::Get, _: &TypedEnv) -> Option<String> {
        s.get(&a.key)
    }

    fn put(s: &mut LruModel, a: &lru::Put, _: &TypedEnv) -> Option<String> {
        s.put(&a.key, &a.value)
    }

    fn remove(s: &mut LruModel, a: &lru::Remove, _: &TypedEnv) -> Option<String> {
        s.remove(&a.key)
    }

    fn contains(s: &mut LruModel, a: &lru::Contains, _: &TypedEnv) -> bool {
        s.contains(&a.key)
    }

    fn len(s: &mut LruModel, _: &lru::Len, _: &TypedEnv) -> usize {
        s.len()
    }
}

impl lru::LruSutInterp for LruLockstep {
    type Sut = LruCache;

    fn get(s: &mut LruCache, a: &lru::Get, _: &TypedEnv) -> Option<String> {
        s.get(&a.key)
    }

    fn put(s: &mut LruCache, a: &lru::Put, _: &TypedEnv) -> Option<String> {
        s.put(&a.key, &a.value)
    }

    fn remove(s: &mut LruCache, a: &lru::Remove, _: &TypedEnv) -> Option<String> {
        s.remove(&a.key)
    }

    fn contains(s: &mut LruCache, a: &lru::Contains, _: &TypedEnv) -> bool {
        s.contains(&a.key)
    }

    fn len(s: &mut LruCache, _: &lru::Len, _: &TypedEnv) -> usize {
        s.len()
    }
}

// ============================================================================
// LockstepModel
// ============================================================================

impl LockstepModel for LruLockstep {
    type ModelState = LruModel;
    type Sut = LruCache;

    fn init_model() -> LruModel {
        LruModel::new(LRU_CAPACITY)
    }
    fn init_sut() -> LruCache {
        LruCache::new(LRU_CAPACITY)
    }

    fn gen_action(state: &LruModel, _env: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        let keys: Vec<String> = state.map.keys().cloned().collect();

        // Mix existing keys with new keys for interesting interactions
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

        prop_oneof![
            3 => ks2.prop_map(|k| lru::get(lru::Get { key: k })),
            3 => (key_strat, proptest::sample::select(vec!["v1", "v2", "v3"]))
                .prop_map(|(k, v)| lru::put(lru::Put { key: k, value: v.to_string() })),
            2 => ks3.prop_map(|k| lru::remove(lru::Remove { key: k })),
            2 => ks4.prop_map(|k| lru::contains(lru::Contains { key: k })),
            1 => Just(lru::len(lru::Len)),
        ]
        .boxed()
    }

    fn step_model(
        state: &mut LruModel,
        action: &dyn AnyAction,
        env: &TypedEnv,
    ) -> Box<dyn Any> {
        lru::dispatch_model::<LruLockstep>(state, action, env)
    }

    fn step_sut(sut: &mut LruCache, action: &dyn AnyAction, env: &TypedEnv) -> Box<dyn Any> {
        lru::dispatch_sut::<LruLockstep>(sut, action, env)
    }
}

// ============================================================================
// ConcurrentLockstepModel
// ============================================================================

#[cfg(feature = "concurrent")]
impl proptest_lockstep::concurrent::ConcurrentLockstepModel for LruLockstep {
    fn step_sut_send(
        sut: &mut LruCache,
        action: &dyn AnyAction,
        env: &TypedEnv,
    ) -> Box<dyn Any + Send> {
        lru::dispatch_sut_send::<LruLockstep>(sut, action, env)
    }
}

fn main() {
    println!("Run with `cargo test --example lru_cache`");
    println!("  or `cargo test --example lru_cache --features concurrent`");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Sequential lockstep test: verify the LRU cache matches the
    /// model under sequential operations including eviction.
    #[test]
    fn lockstep_lru_cache() {
        proptest_lockstep::runner::run_lockstep_test::<LruLockstep>(1..50);
    }
}

#[cfg(all(test, feature = "concurrent"))]
mod concurrent_tests {
    use super::*;
    use proptest_lockstep::concurrent::{
        lockstep_concurrent, lockstep_concurrent_with_check, lockstep_linearizable,
        ConcurrentConfig, SplitStrategy,
    };

    /// Crash-absence: concurrent get/put/remove doesn't panic.
    #[test]
    fn concurrent_lru_crash_absence() {
        lockstep_concurrent::<LruLockstep>(ConcurrentConfig {
            iterations: 100,
            prefix_len: 5,
            branch_len: 4,
            branch_count: 2,
            split_strategy: SplitStrategy::RoundRobin,
            ..Default::default()
        });
    }

    /// Final-state check: after concurrent operations, the cache
    /// respects its capacity bound and internal consistency.
    #[test]
    fn concurrent_lru_final_check() {
        lockstep_concurrent_with_check::<LruLockstep, _>(
            ConcurrentConfig {
                iterations: 100,
                prefix_len: 3,
                branch_len: 5,
                branch_count: 2,
                split_strategy: SplitStrategy::Random { seed: 42 },
                ..Default::default()
            },
            |sut: &LruCache| {
                assert!(
                    sut.len() <= LRU_CAPACITY,
                    "Cache exceeds capacity: {} > {}",
                    sut.len(),
                    LRU_CAPACITY
                );
            },
        );
    }

    /// Linearizability: every concurrent get/put/remove interleaving
    /// is consistent with some sequential ordering.
    #[test]
    fn concurrent_lru_linearizable() {
        lockstep_linearizable::<LruLockstep>(ConcurrentConfig {
            iterations: 50,
            prefix_len: 3,
            branch_len: 3,
            branch_count: 2,
            split_strategy: SplitStrategy::RoundRobin,
            ..Default::default()
        });
    }

    /// ConflictMaximizing: model-guided scheduling places conflicting
    /// operations (get + put on the same key, or puts that trigger
    /// eviction) on different branches.
    #[test]
    fn concurrent_lru_conflict_maximizing() {
        lockstep_linearizable::<LruLockstep>(ConcurrentConfig {
            iterations: 50,
            prefix_len: 3,
            branch_len: 4,
            branch_count: 2,
            split_strategy: SplitStrategy::ConflictMaximizing,
            ..Default::default()
        });
    }
}
