#![allow(dead_code)]
//! Coverage-guided generation demonstration.
//!
//! Tests a bounded counter with coverage-guided generation. The
//! coverage key tracks the counter value, guiding generation toward
//! boundary states (near 0 and near max) that random generation
//! rarely hits.
//!
//! Run with: `cargo test --example coverage_guided`

use std::any::Any;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;
use proptest_lockstep::coverage::{CoverageGuidedModel, CoverageConfig};

// ============================================================================
// Bounded counter -- SUT
// ============================================================================

/// A counter with a maximum value. Increment saturates at max.
#[derive(Debug)]
struct BoundedCounter {
    value: u32,
    max: u32,
}

impl BoundedCounter {
    fn new(max: u32) -> Self { BoundedCounter { value: 0, max } }
    fn increment(&mut self) -> u32 {
        if self.value < self.max { self.value += 1; }
        self.value
    }
    fn decrement(&mut self) -> u32 {
        if self.value > 0 { self.value -= 1; }
        self.value
    }
    fn get(&self) -> u32 { self.value }
    fn is_at_max(&self) -> bool { self.value >= self.max }
    fn is_at_zero(&self) -> bool { self.value == 0 }
}

// ============================================================================
// Model
// ============================================================================

const MAX_VALUE: u32 = 10;

#[derive(Debug, Clone, PartialEq)]
struct CounterModel {
    value: u32,
}

// ============================================================================
// Actions
// ============================================================================

#[proptest_lockstep::lockstep_actions(state = CounterModel)]
pub mod ctr {
    #[action(real_return = "u32")]
    pub struct Increment;

    #[action(real_return = "u32")]
    pub struct Decrement;

    #[action(real_return = "u32")]
    pub struct Get;

    #[action(real_return = "bool")]
    pub struct IsAtMax;

    #[action(real_return = "bool")]
    pub struct IsAtZero;
}

// ============================================================================
// Interpreters
// ============================================================================

#[derive(Debug, Clone)]
struct CounterLockstep;

impl ctr::CtrModelInterp for CounterLockstep {
    type State = CounterModel;
    fn increment(s: &mut CounterModel, _: &ctr::Increment, _: &TypedEnv) -> u32 {
        if s.value < MAX_VALUE { s.value += 1; }
        s.value
    }
    fn decrement(s: &mut CounterModel, _: &ctr::Decrement, _: &TypedEnv) -> u32 {
        if s.value > 0 { s.value -= 1; }
        s.value
    }
    fn get(s: &mut CounterModel, _: &ctr::Get, _: &TypedEnv) -> u32 { s.value }
    fn is_at_max(s: &mut CounterModel, _: &ctr::IsAtMax, _: &TypedEnv) -> bool {
        s.value >= MAX_VALUE
    }
    fn is_at_zero(s: &mut CounterModel, _: &ctr::IsAtZero, _: &TypedEnv) -> bool {
        s.value == 0
    }
}

impl ctr::CtrSutInterp for CounterLockstep {
    type Sut = BoundedCounter;
    fn increment(s: &mut BoundedCounter, _: &ctr::Increment, _: &TypedEnv) -> u32 {
        s.increment()
    }
    fn decrement(s: &mut BoundedCounter, _: &ctr::Decrement, _: &TypedEnv) -> u32 {
        s.decrement()
    }
    fn get(s: &mut BoundedCounter, _: &ctr::Get, _: &TypedEnv) -> u32 { s.get() }
    fn is_at_max(s: &mut BoundedCounter, _: &ctr::IsAtMax, _: &TypedEnv) -> bool {
        s.is_at_max()
    }
    fn is_at_zero(s: &mut BoundedCounter, _: &ctr::IsAtZero, _: &TypedEnv) -> bool {
        s.is_at_zero()
    }
}

impl LockstepModel for CounterLockstep {
    type ModelState = CounterModel;
    type Sut = BoundedCounter;
    fn init_model() -> CounterModel { CounterModel { value: 0 } }
    fn init_sut() -> BoundedCounter { BoundedCounter::new(MAX_VALUE) }
    fn gen_action(_: &CounterModel, _: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        prop_oneof![
            3 => Just(ctr::increment(ctr::Increment)),
            3 => Just(ctr::decrement(ctr::Decrement)),
            1 => Just(ctr::get(ctr::Get)),
            1 => Just(ctr::is_at_max(ctr::IsAtMax)),
            1 => Just(ctr::is_at_zero(ctr::IsAtZero)),
        ].boxed()
    }
    fn step_model(s: &mut CounterModel, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        ctr::dispatch_model::<CounterLockstep>(s, a, e)
    }
    fn step_sut(s: &mut BoundedCounter, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        ctr::dispatch_sut::<CounterLockstep>(s, a, e)
    }
}

// ============================================================================
// CoverageGuidedModel
// ============================================================================

impl CoverageGuidedModel for CounterLockstep {
    fn coverage_key(state: &CounterModel) -> u64 {
        // Coverage buckets based on counter value regions:
        // - 0 (at zero boundary)
        // - 1..=3 (low)
        // - 4..=6 (mid)
        // - 7..=9 (high)
        // - 10 (at max boundary)
        let bucket = match state.value {
            0 => 0,
            1..=3 => 1,
            4..=6 => 2,
            7..=9 => 3,
            _ => 4, // at max
        };
        bucket
    }
}

fn main() {
    println!("Run with `cargo test --example coverage_guided`");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Coverage-guided test: tracks which counter value regions
    /// are explored and reports coverage statistics.
    #[test]
    fn coverage_guided_counter() {
        let stats = proptest_lockstep::coverage::run_coverage_guided_test::<CounterLockstep>(
            CoverageConfig {
                cases: 100,
                min_ops: 10,
                max_ops: 30,
                candidates_per_step: 10,
            },
        );

        eprintln!("{}", stats);

        // Should visit multiple coverage buckets
        assert!(
            stats.buckets_visited >= 3,
            "Should visit at least 3 coverage buckets (zero, low, mid), got {}",
            stats.buckets_visited,
        );
    }

    /// Standard lockstep also passes (coverage guidance doesn't
    /// affect correctness, only exploration).
    #[test]
    fn standard_lockstep_also_passes() {
        proptest_lockstep::runner::run_lockstep_test::<CounterLockstep>(1..30);
    }
}
