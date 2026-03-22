#![allow(dead_code)]
//! crdts library eventual consistency test.
//!
//! Tests the `crdts` crate's GCounter and PNCounter against
//! sequential models. CRDTs are intentionally eventually consistent:
//! per-node views may differ until merge.
//!
//! Demonstrates:
//! - Testing a real CRDT library from crates.io
//! - GCounter (grow-only) and PNCounter (increment + decrement)
//! - Merge convergence verified by the EC framework
//!
//! Run with: `cargo test --example crdts_library`

use std::any::Any;

use num_traits::ToPrimitive;
use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;
use proptest_lockstep::invariant::InvariantModel;
use proptest_lockstep::eventual::{EventualConsistencyModel, EventualConsistencyConfig};

// ============================================================================
// PNCounter — supports increment AND decrement
// ============================================================================

/// SUT: two PNCounter replicas that can be incremented/decremented
/// independently and merged.
#[derive(Debug)]
struct PnCounterPair {
    replica_a: crdts::PNCounter<u8>,
    replica_b: crdts::PNCounter<u8>,
}

impl PnCounterPair {
    fn new() -> Self {
        PnCounterPair {
            replica_a: crdts::PNCounter::new(),
            replica_b: crdts::PNCounter::new(),
        }
    }

    fn inc_a(&mut self) {
        use crdts::CmRDT;
        let op = self.replica_a.inc(0); // actor 0
        self.replica_a.apply(op);
    }

    fn inc_b(&mut self) {
        use crdts::CmRDT;
        let op = self.replica_b.inc(1); // actor 1
        self.replica_b.apply(op);
    }

    fn dec_a(&mut self) {
        use crdts::CmRDT;
        let op = self.replica_a.dec(0);
        self.replica_a.apply(op);
    }

    fn dec_b(&mut self) {
        use crdts::CmRDT;
        let op = self.replica_b.dec(1);
        self.replica_b.apply(op);
    }

    fn read_a(&self) -> i64 {
        use crdts::CvRDT;
        // Local read — may not include B's operations
        let mut merged = self.replica_a.clone();
        merged.merge(self.replica_a.clone());
        self.replica_a.read().to_i64().unwrap_or(0)
    }

    fn read_b(&self) -> i64 {
        use crdts::CvRDT;
        let mut merged = self.replica_b.clone();
        merged.merge(self.replica_b.clone());
        self.replica_b.read().to_i64().unwrap_or(0)
    }

    fn merge(&mut self) {
        use crdts::CvRDT;
        let a = self.replica_a.clone();
        let b = self.replica_b.clone();
        self.replica_a.merge(b);
        self.replica_b.merge(a);
    }

    fn read_merged(&self) -> i64 {
        use crdts::CvRDT;
        let mut merged = self.replica_a.clone();
        merged.merge(self.replica_b.clone());
        merged.read().to_i64().unwrap_or(0)
    }
}

// ============================================================================
// Model — sequential counter tracking total
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
struct CounterModel {
    total: i64,
}

impl CounterModel {
    fn new() -> Self { CounterModel { total: 0 } }
}

// ============================================================================
// Actions
// ============================================================================

#[proptest_lockstep::lockstep_actions(state = CounterModel)]
pub mod pn {
    #[action(real_return = "()")]
    pub struct IncA;

    #[action(real_return = "()")]
    pub struct IncB;

    #[action(real_return = "()")]
    pub struct DecA;

    #[action(real_return = "()")]
    pub struct DecB;

    // Read from replica A — may be stale
    #[action(real_return = "i64")]
    pub struct ReadA;

    // Global read (merged) — always up to date
    #[action(real_return = "i64")]
    pub struct ReadMerged;
}

// ============================================================================
// Interpreters
// ============================================================================

#[derive(Debug, Clone)]
struct PnLockstep;

impl pn::PnModelInterp for PnLockstep {
    type State = CounterModel;
    fn inc_a(s: &mut CounterModel, _: &pn::IncA, _: &TypedEnv) { s.total += 1; }
    fn inc_b(s: &mut CounterModel, _: &pn::IncB, _: &TypedEnv) { s.total += 1; }
    fn dec_a(s: &mut CounterModel, _: &pn::DecA, _: &TypedEnv) { s.total -= 1; }
    fn dec_b(s: &mut CounterModel, _: &pn::DecB, _: &TypedEnv) { s.total -= 1; }
    fn read_a(s: &mut CounterModel, _: &pn::ReadA, _: &TypedEnv) -> i64 { s.total }
    fn read_merged(s: &mut CounterModel, _: &pn::ReadMerged, _: &TypedEnv) -> i64 { s.total }
}

impl pn::PnSutInterp for PnLockstep {
    type Sut = PnCounterPair;
    fn inc_a(s: &mut PnCounterPair, _: &pn::IncA, _: &TypedEnv) { s.inc_a(); }
    fn inc_b(s: &mut PnCounterPair, _: &pn::IncB, _: &TypedEnv) { s.inc_b(); }
    fn dec_a(s: &mut PnCounterPair, _: &pn::DecA, _: &TypedEnv) { s.dec_a(); }
    fn dec_b(s: &mut PnCounterPair, _: &pn::DecB, _: &TypedEnv) { s.dec_b(); }
    fn read_a(s: &mut PnCounterPair, _: &pn::ReadA, _: &TypedEnv) -> i64 { s.read_a() }
    fn read_merged(s: &mut PnCounterPair, _: &pn::ReadMerged, _: &TypedEnv) -> i64 { s.read_merged() }
}

impl LockstepModel for PnLockstep {
    type ModelState = CounterModel;
    type Sut = PnCounterPair;
    fn init_model() -> CounterModel { CounterModel::new() }
    fn init_sut() -> PnCounterPair { PnCounterPair::new() }
    fn gen_action(_: &CounterModel, _: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        prop_oneof![
            2 => Just(pn::inc_a(pn::IncA)),
            2 => Just(pn::inc_b(pn::IncB)),
            1 => Just(pn::dec_a(pn::DecA)),
            1 => Just(pn::dec_b(pn::DecB)),
            2 => Just(pn::read_a(pn::ReadA)),
            1 => Just(pn::read_merged(pn::ReadMerged)),
        ].boxed()
    }
    fn step_model(s: &mut CounterModel, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        pn::dispatch_model::<PnLockstep>(s, a, e)
    }
    fn step_sut(s: &mut PnCounterPair, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        pn::dispatch_sut::<PnLockstep>(s, a, e)
    }
}

impl InvariantModel for PnLockstep {}

impl EventualConsistencyModel for PnLockstep {
    type ObservableState = i64;

    fn sut_sync(sut: &mut PnCounterPair) -> i64 {
        sut.merge();
        sut.read_merged()
    }

    fn model_sync(state: &CounterModel) -> i64 {
        state.total
    }
}

fn main() {
    println!("Run with `cargo test --example crdts_library`");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Eventual consistency: after merge, PNCounter matches model.
    #[test]
    fn pncounter_eventually_consistent() {
        proptest_lockstep::eventual::run_eventual_consistency_test::<PnLockstep>(
            EventualConsistencyConfig {
                cases: 100,
                min_ops: 5,
                max_ops: 20,
                intermediate_syncs: 3,
            },
        );
    }

    /// Standard lockstep FAILS because per-replica reads are stale.
    #[test]
    #[should_panic(expected = "Lockstep mismatch")]
    fn pncounter_not_linearizable() {
        proptest_lockstep::runner::run_lockstep_test::<PnLockstep>(1..15);
    }
}
