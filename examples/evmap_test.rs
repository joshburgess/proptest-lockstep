#![allow(dead_code)]
//! evmap eventual consistency test -- testing a real EC crate.
//!
//! Tests `evmap` -- a lock-free, eventually consistent concurrent map.
//! Writers update one copy while readers see the other. Writes become
//! visible only after `refresh()`.
//!
//! This is the perfect demonstration of the eventual consistency
//! framework:
//! - Standard lockstep FAILS (reads return stale data -- by design!)
//! - Eventual consistency PASSES (after sync/refresh, state converges)
//!
//! This proves the framework correctly handles a real eventually-
//! consistent crate from crates.io.
//!
//! Run with: `cargo test --example evmap_test`

use std::any::Any;
use std::collections::HashMap;

use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;
use proptest_lockstep::invariant::InvariantModel;
use proptest_lockstep::eventual::{EventualConsistencyModel, EventualConsistencyConfig};

// ============================================================================
// evmap wrapper -- combines read + write handles
// ============================================================================

/// Wraps evmap's separate read/write handles into a single struct
/// that our framework can use as the SUT.
struct EvmapStore {
    reader: evmap::ReadHandle<String, String>,
    writer: evmap::WriteHandle<String, String>,
}

impl EvmapStore {
    fn new() -> Self {
        let (reader, writer) = evmap::new();
        EvmapStore { reader, writer }
    }

    fn insert(&mut self, key: &str, value: &str) {
        // evmap supports multiple values per key; we use empty + insert
        // to simulate single-value semantics
        self.writer.empty(key.to_string());
        self.writer.insert(key.to_string(), value.to_string());
        // NOTE: not calling refresh() -- write is pending!
    }

    fn get(&self, key: &str) -> Option<String> {
        // Reads from the reader handle -- may return stale data
        self.reader
            .get_one(key)
            .map(|guard| guard.clone())
    }

    fn contains_key(&self, key: &str) -> bool {
        self.reader.contains_key(key)
    }

    fn refresh(&mut self) {
        self.writer.refresh();
    }

    fn snapshot(&self) -> HashMap<String, String> {
        let mut result = HashMap::new();
        if let Some(map_ref) = self.reader.read() {
            for (k, vs) in map_ref.iter() {
                if let Some(v) = vs.iter().next() {
                    result.insert(k.clone(), v.clone());
                }
            }
        }
        result
    }
}

impl std::fmt::Debug for EvmapStore {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EvmapStore").finish()
    }
}

// ============================================================================
// Model -- sequential HashMap (always up-to-date)
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
struct EvmapModel {
    data: HashMap<String, String>,
}

impl EvmapModel {
    fn new() -> Self {
        EvmapModel { data: HashMap::new() }
    }
}

// ============================================================================
// Actions
// ============================================================================

#[proptest_lockstep::lockstep_actions(state = EvmapModel)]
pub mod em {
    #[action(real_return = "()")]
    pub struct Insert {
        pub key: String,
        pub value: String,
    }

    // Reads may return stale data from evmap -- that's expected!
    #[action(real_return = "Option<String>")]
    pub struct Get {
        pub key: String,
    }

    #[action(real_return = "bool")]
    pub struct ContainsKey {
        pub key: String,
    }
}

// ============================================================================
// Interpreters
// ============================================================================

#[derive(Debug, Clone)]
struct EvmapLockstep;

impl em::EmModelInterp for EvmapLockstep {
    type State = EvmapModel;

    fn insert(s: &mut EvmapModel, a: &em::Insert, _: &TypedEnv) {
        s.data.insert(a.key.clone(), a.value.clone());
    }

    fn get(s: &mut EvmapModel, a: &em::Get, _: &TypedEnv) -> Option<String> {
        s.data.get(&a.key).cloned()
    }

    fn contains_key(s: &mut EvmapModel, a: &em::ContainsKey, _: &TypedEnv) -> bool {
        s.data.contains_key(&a.key)
    }
}

impl em::EmSutInterp for EvmapLockstep {
    type Sut = EvmapStore;

    fn insert(s: &mut EvmapStore, a: &em::Insert, _: &TypedEnv) {
        s.insert(&a.key, &a.value);
    }

    fn get(s: &mut EvmapStore, a: &em::Get, _: &TypedEnv) -> Option<String> {
        s.get(&a.key)
    }

    fn contains_key(s: &mut EvmapStore, a: &em::ContainsKey, _: &TypedEnv) -> bool {
        s.contains_key(&a.key)
    }
}

impl LockstepModel for EvmapLockstep {
    type ModelState = EvmapModel;
    type Sut = EvmapStore;

    fn init_model() -> EvmapModel { EvmapModel::new() }
    fn init_sut() -> EvmapStore { EvmapStore::new() }

    fn gen_action(_: &EvmapModel, _: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        let keys = vec!["a", "b", "c", "d"];
        let vals = vec!["1", "2", "3"];
        let ks = proptest::sample::select(keys.clone()).prop_map(|s| s.to_string());
        let ks2 = proptest::sample::select(keys.clone()).prop_map(|s| s.to_string());
        let ks3 = proptest::sample::select(keys).prop_map(|s| s.to_string());
        let vs = proptest::sample::select(vals).prop_map(|s| s.to_string());
        prop_oneof![
            3 => (ks, vs).prop_map(|(k, v)| em::insert(em::Insert { key: k, value: v })),
            3 => ks2.prop_map(|k| em::get(em::Get { key: k })),
            1 => ks3.prop_map(|k| em::contains_key(em::ContainsKey { key: k })),
        ].boxed()
    }

    fn step_model(s: &mut EvmapModel, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        em::dispatch_model::<EvmapLockstep>(s, a, e)
    }

    fn step_sut(s: &mut EvmapStore, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        em::dispatch_sut::<EvmapLockstep>(s, a, e)
    }
}

impl InvariantModel for EvmapLockstep {}

// ============================================================================
// EventualConsistencyModel
// ============================================================================

impl EventualConsistencyModel for EvmapLockstep {
    type ObservableState = HashMap<String, String>;

    fn sut_sync(sut: &mut EvmapStore) -> HashMap<String, String> {
        // refresh() makes all pending writes visible to readers
        sut.refresh();
        sut.snapshot()
    }

    fn model_sync(state: &EvmapModel) -> HashMap<String, String> {
        state.data.clone()
    }
}

fn main() {
    println!("Run with `cargo test --example evmap_test`");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Eventual consistency test: reads may be stale, but after
    /// refresh() the evmap matches the model.
    #[test]
    fn evmap_eventually_consistent() {
        proptest_lockstep::eventual::run_eventual_consistency_test::<EvmapLockstep>(
            EventualConsistencyConfig {
                cases: 200,
                min_ops: 5,
                max_ops: 20,
                intermediate_syncs: 3,
            },
        );
    }

    /// Standard lockstep FAILS because evmap returns stale reads.
    /// This proves that evmap is NOT linearizable (by design) --
    /// and our framework correctly detects this.
    #[test]
    #[should_panic(expected = "Lockstep mismatch")]
    fn evmap_not_linearizable() {
        proptest_lockstep::runner::run_lockstep_test::<EvmapLockstep>(1..20);
    }
}
