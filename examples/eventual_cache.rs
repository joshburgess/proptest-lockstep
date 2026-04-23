#![allow(dead_code)]
//! Eventually-consistent cache lockstep test.
//!
//! Tests a write-through cache that buffers writes and may serve
//! stale reads until a `sync` operation flushes pending writes.
//! This is intentionally NOT linearizable -- reads can return stale
//! data -- but it IS eventually consistent: after sync, the cache
//! matches the model.
//!
//! Run with: `cargo test --example eventual_cache`

use std::any::Any;
use std::collections::HashMap;

use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;
use proptest_lockstep::invariant::InvariantModel;
use proptest_lockstep::eventual::{EventualConsistencyModel, EventualConsistencyConfig};

// ============================================================================
// Eventually-consistent cache -- SUT
// ============================================================================

/// A cache that buffers writes. Reads may return stale data until
/// `sync` is called. After sync, the cache reflects all writes.
#[derive(Debug)]
struct LazyCache {
    /// The "committed" store (what sync reads from).
    store: HashMap<String, String>,
    /// Pending writes not yet visible to reads.
    pending: Vec<(String, String)>,
}

impl LazyCache {
    fn new() -> Self {
        LazyCache {
            store: HashMap::new(),
            pending: Vec::new(),
        }
    }

    fn write(&mut self, key: &str, value: &str) {
        // Write goes to pending buffer, not directly to store
        self.pending.push((key.to_string(), value.to_string()));
    }

    fn read(&self, key: &str) -> Option<String> {
        // Reads from store only -- pending writes are invisible!
        self.store.get(key).cloned()
    }

    fn sync(&mut self) {
        // Flush all pending writes to the store
        for (k, v) in self.pending.drain(..) {
            self.store.insert(k, v);
        }
    }

    fn snapshot(&self) -> HashMap<String, String> {
        let mut result = self.store.clone();
        // Include pending writes in the snapshot
        for (k, v) in &self.pending {
            result.insert(k.clone(), v.clone());
        }
        result
    }
}

// ============================================================================
// Model -- sequential store (always up-to-date)
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
struct CacheModel {
    data: HashMap<String, String>,
}

impl CacheModel {
    fn new() -> Self {
        CacheModel {
            data: HashMap::new(),
        }
    }
}

// ============================================================================
// Actions
// ============================================================================

#[proptest_lockstep::lockstep_actions(state = CacheModel)]
pub mod cache {
    #[action(real_return = "()")]
    pub struct Write {
        pub key: String,
        pub value: String,
    }

    // Read may return stale data from the SUT -- that's expected!
    // We still track it for the lockstep framework, but the
    // eventual consistency runner doesn't check per-step bridges.
    #[action(real_return = "Option<String>")]
    pub struct Read {
        pub key: String,
    }
}

// ============================================================================
// Interpreters
// ============================================================================

#[derive(Debug, Clone)]
struct CacheLockstep;

impl cache::CacheModelInterp for CacheLockstep {
    type State = CacheModel;

    fn write(s: &mut CacheModel, a: &cache::Write, _: &TypedEnv) {
        s.data.insert(a.key.clone(), a.value.clone());
    }

    fn read(s: &mut CacheModel, a: &cache::Read, _: &TypedEnv) -> Option<String> {
        s.data.get(&a.key).cloned()
    }
}

impl cache::CacheSutInterp for CacheLockstep {
    type Sut = LazyCache;

    fn write(s: &mut LazyCache, a: &cache::Write, _: &TypedEnv) {
        s.write(&a.key, &a.value);
    }

    fn read(s: &mut LazyCache, a: &cache::Read, _: &TypedEnv) -> Option<String> {
        s.read(&a.key) // May return stale data!
    }
}

impl LockstepModel for CacheLockstep {
    type ModelState = CacheModel;
    type Sut = LazyCache;

    fn init_model() -> CacheModel { CacheModel::new() }
    fn init_sut() -> LazyCache { LazyCache::new() }

    fn gen_action(_: &CacheModel, _: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        let keys = vec!["x", "y", "z"];
        let vals = vec!["a", "b", "c"];
        let ks = proptest::sample::select(keys.clone()).prop_map(|s| s.to_string());
        let ks2 = proptest::sample::select(keys).prop_map(|s| s.to_string());
        let vs = proptest::sample::select(vals).prop_map(|s| s.to_string());
        prop_oneof![
            3 => (ks, vs).prop_map(|(k, v)| cache::write(cache::Write { key: k, value: v })),
            2 => ks2.prop_map(|k| cache::read(cache::Read { key: k })),
        ].boxed()
    }

    fn step_model(s: &mut CacheModel, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        cache::dispatch_model::<CacheLockstep>(s, a, e)
    }

    fn step_sut(s: &mut LazyCache, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        cache::dispatch_sut::<CacheLockstep>(s, a, e)
    }
}

impl InvariantModel for CacheLockstep {}

// ============================================================================
// EventualConsistencyModel
// ============================================================================

impl EventualConsistencyModel for CacheLockstep {
    /// After sync, we observe the full key-value contents.
    type ObservableState = HashMap<String, String>;

    fn sut_sync(sut: &mut LazyCache) -> HashMap<String, String> {
        sut.sync();
        sut.store.clone()
    }

    fn model_sync(state: &CacheModel) -> HashMap<String, String> {
        state.data.clone()
    }
}

fn main() {
    println!("Run with `cargo test --example eventual_cache`");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Eventual consistency test: reads may be stale, but after
    /// sync the cache matches the model.
    #[test]
    fn eventual_cache_converges() {
        proptest_lockstep::eventual::run_eventual_consistency_test::<CacheLockstep>(
            EventualConsistencyConfig {
                cases: 200,
                min_ops: 5,
                max_ops: 30,
                intermediate_syncs: 3,
            },
        );
    }

    /// This test would FAIL with standard lockstep (bridge check at
    /// every step), because reads return stale data. But it PASSES
    /// with eventual consistency checking.
    #[test]
    #[should_panic(expected = "Lockstep mismatch")]
    fn standard_lockstep_fails_on_stale_reads() {
        // Standard lockstep catches the "stale read" as a bug --
        // but for an eventually-consistent system, this is expected.
        proptest_lockstep::runner::run_lockstep_test::<CacheLockstep>(1..30);
    }
}
