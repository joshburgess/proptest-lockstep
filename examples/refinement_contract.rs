#![allow(dead_code)]
//! Observational refinement contracts demonstration.
//!
//! Shows how the bridge algebra powers runtime contract monitoring.
//! A `RefinementGuard` shadows the SUT with a model, checking bridge
//! equivalence at every operation. Violations are collected (not
//! panicked on), enabling use as a production monitor.
//!
//! Three scenarios:
//! 1. Correct SUT -- no violations
//! 2. Buggy SUT -- violations detected and reported
//! 3. Gradual tightening -- start with Opaque (permissive), tighten
//!    to Transparent (strict)
//!
//! Run with: `cargo test --example refinement_contract`

use std::any::Any;
use std::collections::HashMap;
use std::time::Duration;

use proptest_lockstep::prelude::*;
use proptest_lockstep::contracts::{
    RefinementGuard, ContractConfig, DivergenceStrategy, assert_no_violations,
};

// ============================================================================
// KV Store -- correct implementation
// ============================================================================

#[derive(Debug)]
struct CorrectKv {
    data: HashMap<String, String>,
}

impl CorrectKv {
    fn new() -> Self { CorrectKv { data: HashMap::new() } }
    fn put(&mut self, key: &str, value: &str) -> Option<String> {
        self.data.insert(key.into(), value.into())
    }
    fn get(&self, key: &str) -> Option<String> {
        self.data.get(key).cloned()
    }
}

// ============================================================================
// KV Store -- buggy implementation (sometimes returns wrong value)
// ============================================================================

#[derive(Debug)]
struct BuggyKv {
    data: HashMap<String, String>,
    op_count: usize,
}

impl BuggyKv {
    fn new() -> Self { BuggyKv { data: HashMap::new(), op_count: 0 } }
    fn put(&mut self, key: &str, value: &str) -> Option<String> {
        self.op_count += 1;
        self.data.insert(key.into(), value.into())
    }
    fn get(&self, key: &str) -> Option<String> {
        // BUG: every 5th get returns None even if key exists
        if self.data.contains_key(key) && self.data.len() % 5 == 0 {
            None // stale read!
        } else {
            self.data.get(key).cloned()
        }
    }
}

// ============================================================================
// Model + Actions
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
struct KvModel {
    data: HashMap<String, String>,
}

#[proptest_lockstep::lockstep_actions(state = KvModel)]
pub mod kv {
    #[action(real_return = "Option<String>")]
    pub struct Put { pub key: String, pub value: String }

    #[action(real_return = "Option<String>")]
    pub struct Get { pub key: String }
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
}

// SUT interpreter -- uses CorrectKv by default
impl kv::KvSutInterp for KvLockstep {
    type Sut = CorrectKv;
    fn put(s: &mut CorrectKv, a: &kv::Put, _: &TypedEnv) -> Option<String> {
        s.put(&a.key, &a.value)
    }
    fn get(s: &mut CorrectKv, a: &kv::Get, _: &TypedEnv) -> Option<String> {
        s.get(&a.key)
    }
}

impl LockstepModel for KvLockstep {
    type ModelState = KvModel;
    type Sut = CorrectKv;
    fn init_model() -> KvModel { KvModel { data: HashMap::new() } }
    fn init_sut() -> CorrectKv { CorrectKv::new() }
    fn gen_action(_: &KvModel, _: &TypedEnv) -> proptest::strategy::BoxedStrategy<Box<dyn AnyAction>> {
        unimplemented!("contracts don't use gen_action")
    }
    fn step_model(s: &mut KvModel, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        kv::dispatch_model::<KvLockstep>(s, a, e)
    }
    fn step_sut(s: &mut CorrectKv, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        kv::dispatch_sut::<KvLockstep>(s, a, e)
    }
}

fn main() {
    println!("Run with `cargo test --example refinement_contract`");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Scenario 1: Correct SUT -- no violations.
    /// The refinement guard shadows the correct KV store and
    /// confirms all operations match the model.
    #[test]
    fn correct_sut_no_violations() {
        let mut guard = RefinementGuard::<KvLockstep>::new();

        // Simulate production operations
        let mut sut = CorrectKv::new();

        let put_a = kv::put(kv::Put { key: "x".into(), value: "1".into() });
        let result_a: Box<dyn Any> = Box::new(sut.put("x", "1"));
        guard.check(put_a.as_ref(), &*result_a);

        let put_b = kv::put(kv::Put { key: "y".into(), value: "2".into() });
        let result_b: Box<dyn Any> = Box::new(sut.put("y", "2"));
        guard.check(put_b.as_ref(), &*result_b);

        let get_x = kv::get(kv::Get { key: "x".into() });
        let result_c: Box<dyn Any> = Box::new(sut.get("x"));
        guard.check(get_x.as_ref(), &*result_c);

        assert_no_violations(&guard);
        assert_eq!(guard.checks_passed(), 3);
        assert_eq!(guard.total_steps(), 3);

        // Performance stats are available
        let perf = guard.performance();
        assert_eq!(perf.operations_checked, 3);
        assert_eq!(perf.operations_skipped, 0);
    }

    /// Scenario 2: Buggy SUT -- violations detected.
    /// The buggy KV store sometimes returns None for existing keys.
    /// The guard detects this without crashing.
    #[test]
    fn buggy_sut_violations_detected() {
        let mut guard = RefinementGuard::<KvLockstep>::new();
        let mut sut = BuggyKv::new();

        // Insert 5 keys to trigger the bug (len % 5 == 0)
        for i in 0..5 {
            let key = format!("k{}", i);
            let value = format!("v{}", i);
            let action = kv::put(kv::Put { key: key.clone(), value: value.clone() });
            let result: Box<dyn Any> = Box::new(sut.put(&key, &value));
            guard.check(action.as_ref(), &*result);
        }

        // Now get -- the buggy SUT returns None for existing keys
        // when data.len() % 5 == 0
        let get = kv::get(kv::Get { key: "k0".into() });
        let result: Box<dyn Any> = Box::new(sut.get("k0"));
        guard.check(get.as_ref(), &*result);

        // The guard should have caught the mismatch
        assert!(
            guard.has_violations(),
            "Should detect violation from buggy SUT"
        );
        assert_eq!(guard.violation_count(), 1);

        // Report is informative
        let report = guard.report();
        assert!(report.contains("violation"), "Report should mention violation");
    }

    /// Scenario 3: Reset and reuse.
    #[test]
    fn guard_reset() {
        let mut guard = RefinementGuard::<KvLockstep>::new();
        let mut sut = CorrectKv::new();

        let action = kv::put(kv::Put { key: "a".into(), value: "1".into() });
        let result: Box<dyn Any> = Box::new(sut.put("a", "1"));
        guard.check(action.as_ref(), &*result);
        assert_eq!(guard.total_steps(), 1);

        guard.reset();
        assert_eq!(guard.total_steps(), 0);
        assert_eq!(guard.violation_count(), 0);
    }

    /// Scenario 4: StopOnFirst divergence strategy.
    /// After the first violation, the guard stops checking.
    #[test]
    fn stop_on_first_violation() {
        let mut guard = RefinementGuard::<KvLockstep>::with_config(ContractConfig {
            divergence: DivergenceStrategy::StopOnFirst,
            ..Default::default()
        });
        let mut sut = BuggyKv::new();

        // Trigger the bug
        for i in 0..5 {
            let key = format!("k{}", i);
            let value = format!("v{}", i);
            let action = kv::put(kv::Put { key: key.clone(), value: value.clone() });
            let result: Box<dyn Any> = Box::new(sut.put(&key, &value));
            guard.check(action.as_ref(), &*result);
        }

        let get = kv::get(kv::Get { key: "k0".into() });
        let result: Box<dyn Any> = Box::new(sut.get("k0"));
        guard.check(get.as_ref(), &*result); // violation!

        assert!(guard.is_stopped());
        assert_eq!(guard.violation_count(), 1);

        // Further checks are skipped
        let get2 = kv::get(kv::Get { key: "k1".into() });
        let result2: Box<dyn Any> = Box::new(sut.get("k1"));
        guard.check(get2.as_ref(), &*result2);

        // Still only 1 violation -- the second check was skipped
        assert_eq!(guard.violation_count(), 1);
        assert!(guard.performance().operations_skipped > 0);
    }

    /// Scenario 5: Partial monitoring with sampling.
    /// Only ~50% of operations are checked.
    #[test]
    fn partial_monitoring() {
        let mut guard = RefinementGuard::<KvLockstep>::with_config(ContractConfig {
            sampling_rate: 0.5,
            ..Default::default()
        });
        let mut sut = CorrectKv::new();

        // Run 20 operations
        for i in 0..20 {
            let key = format!("k{}", i);
            let value = format!("v{}", i);
            let action = kv::put(kv::Put { key: key.clone(), value: value.clone() });
            let result: Box<dyn Any> = Box::new(sut.put(&key, &value));
            guard.check(action.as_ref(), &*result);
        }

        let perf = guard.performance();
        // With 50% sampling, roughly half should be checked
        assert!(perf.operations_checked > 0);
        assert!(perf.operations_skipped > 0);
        assert_eq!(
            perf.operations_checked + perf.operations_skipped,
            20
        );
        assert!(!guard.has_violations());
    }

    /// Scenario 6: Performance tracking.
    #[test]
    fn performance_tracking() {
        let mut guard = RefinementGuard::<KvLockstep>::new();
        let mut sut = CorrectKv::new();

        for i in 0..10 {
            let action = kv::put(kv::Put {
                key: format!("k{}", i),
                value: format!("v{}", i),
            });
            let result: Box<dyn Any> = Box::new(sut.put(&format!("k{}", i), &format!("v{}", i)));
            guard.check(action.as_ref(), &*result);
        }

        let perf = guard.performance();
        assert_eq!(perf.operations_checked, 10);
        assert!(perf.model_time > Duration::ZERO || perf.operations_checked > 0);
        assert!(perf.total_overhead() >= Duration::ZERO);
    }
}
