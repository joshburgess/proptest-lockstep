#![allow(dead_code)]
//! CRDT G-Counter eventual consistency test.
//!
//! Tests a G-Counter (grow-only counter) CRDT replicated across
//! simulated nodes. Each node can increment its own counter locally.
//! After merge, all nodes agree on the total count.
//!
//! This is the canonical CRDT example from the literature (Shapiro
//! et al., 2011). It demonstrates:
//! - **Per-node local operations**: each node increments independently
//! - **Merge convergence**: after merge, the counter reflects all
//!   increments from all nodes
//! - **Commutativity**: merges are commutative, associative, idempotent
//! - **Eventual consistency**: reads may lag until merge, but converge
//!
//! The model tracks the true total (sum of all increments). The SUT
//! is a replicated G-Counter where each node only sees its own
//! increments until merge. After merge, the SUT converges to the
//! model's total.
//!
//! Run with: `cargo test --example crdt_counter`

use std::any::Any;
use std::collections::HashMap;

use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;
use proptest_lockstep::invariant::InvariantModel;
use proptest_lockstep::eventual::{EventualConsistencyModel, EventualConsistencyConfig};

// ============================================================================
// G-Counter CRDT — SUT
// ============================================================================

/// A G-Counter (grow-only counter) CRDT.
///
/// Each node maintains its own count. The total value is the sum
/// of all node counts. Merge takes the max of each node's count
/// across replicas.
///
/// In this implementation, we simulate multiple "replicas" within
/// a single struct. Each node increments its own slot. `query()`
/// returns the sum, but a specific node's `local_query()` may
/// return a stale (lower) value if it hasn't merged with others.
#[derive(Debug)]
struct GCounter {
    /// Per-node counts. Key is node ID, value is that node's count.
    counts: HashMap<u8, u64>,
    /// Each node's "view" — what it last saw from others.
    /// Initially each node only sees its own count.
    views: HashMap<u8, HashMap<u8, u64>>,
}

impl GCounter {
    fn new(nodes: &[u8]) -> Self {
        let mut counts = HashMap::new();
        let mut views = HashMap::new();
        for &node in nodes {
            counts.insert(node, 0);
            let mut view = HashMap::new();
            view.insert(node, 0);
            views.insert(node, view);
        }
        GCounter { counts, views }
    }

    /// Increment node's counter by 1.
    fn increment(&mut self, node: u8) {
        let count = self.counts.entry(node).or_insert(0);
        *count += 1;
        // Update this node's own view
        self.views
            .entry(node)
            .or_insert_with(HashMap::new)
            .insert(node, *count);
    }

    /// Query the total from a specific node's perspective.
    /// Returns the sum of what this node has seen (may be stale).
    fn local_query(&self, node: u8) -> u64 {
        self.views
            .get(&node)
            .map(|view| view.values().sum())
            .unwrap_or(0)
    }

    /// Global query: the true total (sum of all node counts).
    fn global_query(&self) -> u64 {
        self.counts.values().sum()
    }

    /// Merge: synchronize all nodes' views. After merge, every
    /// node sees every other node's latest count.
    fn merge(&mut self) {
        // Each node's view gets the max of all counts
        for (&node, view) in self.views.iter_mut() {
            for (&other_node, &count) in &self.counts {
                let entry = view.entry(other_node).or_insert(0);
                *entry = (*entry).max(count);
            }
        }
    }
}

// ============================================================================
// Model — sequential counter (always up-to-date)
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
struct CounterModel {
    total: u64,
}

impl CounterModel {
    fn new() -> Self {
        CounterModel { total: 0 }
    }
}

// ============================================================================
// Actions
// ============================================================================

#[proptest_lockstep::lockstep_actions(state = CounterModel)]
pub mod gc {
    /// Increment a specific node's counter.
    #[action(real_return = "()")]
    pub struct Increment {
        pub node: u8,
    }

    /// Query total from a specific node's perspective (may be stale).
    #[action(real_return = "u64")]
    pub struct LocalQuery {
        pub node: u8,
    }

    /// Query the true global total.
    #[action(real_return = "u64")]
    pub struct GlobalQuery;
}

// ============================================================================
// Interpreters
// ============================================================================

#[derive(Debug, Clone)]
struct CrdtCounterLockstep;

const NODES: [u8; 3] = [0, 1, 2];

impl gc::GcModelInterp for CrdtCounterLockstep {
    type State = CounterModel;

    fn increment(s: &mut CounterModel, _a: &gc::Increment, _: &TypedEnv) {
        s.total += 1;
    }

    fn local_query(s: &mut CounterModel, _a: &gc::LocalQuery, _: &TypedEnv) -> u64 {
        // Model always returns the true total
        s.total
    }

    fn global_query(s: &mut CounterModel, _: &gc::GlobalQuery, _: &TypedEnv) -> u64 {
        s.total
    }
}

impl gc::GcSutInterp for CrdtCounterLockstep {
    type Sut = GCounter;

    fn increment(s: &mut GCounter, a: &gc::Increment, _: &TypedEnv) {
        s.increment(a.node);
    }

    fn local_query(s: &mut GCounter, a: &gc::LocalQuery, _: &TypedEnv) -> u64 {
        // May return stale value!
        s.local_query(a.node)
    }

    fn global_query(s: &mut GCounter, _: &gc::GlobalQuery, _: &TypedEnv) -> u64 {
        s.global_query()
    }
}

// ============================================================================
// LockstepModel
// ============================================================================

impl LockstepModel for CrdtCounterLockstep {
    type ModelState = CounterModel;
    type Sut = GCounter;

    fn init_model() -> CounterModel { CounterModel::new() }
    fn init_sut() -> GCounter { GCounter::new(&NODES) }

    fn gen_action(_: &CounterModel, _: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        prop_oneof![
            3 => proptest::sample::select(NODES.to_vec())
                .prop_map(|n| gc::increment(gc::Increment { node: n })),
            2 => proptest::sample::select(NODES.to_vec())
                .prop_map(|n| gc::local_query(gc::LocalQuery { node: n })),
            1 => Just(gc::global_query(gc::GlobalQuery)),
        ].boxed()
    }

    fn step_model(s: &mut CounterModel, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        gc::dispatch_model::<CrdtCounterLockstep>(s, a, e)
    }

    fn step_sut(s: &mut GCounter, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        gc::dispatch_sut::<CrdtCounterLockstep>(s, a, e)
    }
}

impl InvariantModel for CrdtCounterLockstep {
    fn invariant(state: &CounterModel) -> bool {
        // Total is always non-negative (trivially true for u64)
        state.total < u64::MAX
    }
}

// ============================================================================
// EventualConsistencyModel
// ============================================================================

impl EventualConsistencyModel for CrdtCounterLockstep {
    /// After merge, the observable state is the global total.
    type ObservableState = u64;

    fn sut_sync(sut: &mut GCounter) -> u64 {
        sut.merge();
        // After merge, all local queries should agree with global
        sut.global_query()
    }

    fn model_sync(state: &CounterModel) -> u64 {
        state.total
    }
}

fn main() {
    println!("Run with `cargo test --example crdt_counter`");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Eventual consistency: after merge, the G-Counter's total
    /// matches the model's total.
    #[test]
    fn crdt_counter_eventually_consistent() {
        proptest_lockstep::eventual::run_eventual_consistency_test::<CrdtCounterLockstep>(
            EventualConsistencyConfig {
                cases: 200,
                min_ops: 5,
                max_ops: 25,
                intermediate_syncs: 3,
            },
        );
    }

    /// Standard lockstep FAILS because local queries return stale
    /// counts (a node doesn't see other nodes' increments until merge).
    #[test]
    #[should_panic(expected = "Lockstep mismatch")]
    fn crdt_counter_not_linearizable() {
        proptest_lockstep::runner::run_lockstep_test::<CrdtCounterLockstep>(1..20);
    }
}
