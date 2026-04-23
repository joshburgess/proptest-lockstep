#![allow(dead_code)]
//! Concurrent counter lockstep test.
//!
//! Tests an atomic counter (`AtomicU64`) against a sequential `u64`
//! model. This is the simplest possible concurrent data structure,
//! demonstrating that even trivial-looking atomics benefit from
//! linearizability checking.
//!
//! Operations:
//! - `Increment`: atomically adds 1 (fetch_add)
//! - `Decrement`: atomically subtracts 1, saturating at 0
//! - `CompareAndSwap`: CAS with expected/new values
//! - `Load`: read the current value
//! - `Reset`: set to 0
//!
//! Run with:
//!   `cargo test --example concurrent_counter`                         (sequential)
//!   `cargo test --example concurrent_counter --features concurrent`   (all tests)

use std::any::Any;
use std::sync::atomic::{AtomicU64, Ordering};

use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;

// ============================================================================
// Atomic counter -- SUT
// ============================================================================

/// A counter backed by `AtomicU64`.
///
/// Supports increment, decrement (saturating), compare-and-swap, load,
/// and reset. Each operation maps to a single atomic instruction.
pub struct AtomicCounter {
    value: AtomicU64,
}

impl AtomicCounter {
    fn new() -> Self {
        AtomicCounter {
            value: AtomicU64::new(0),
        }
    }

    fn increment(&self) -> u64 {
        self.value.fetch_add(1, Ordering::SeqCst)
    }

    fn decrement(&self) -> u64 {
        loop {
            let current = self.value.load(Ordering::SeqCst);
            if current == 0 {
                return 0;
            }
            if self
                .value
                .compare_exchange_weak(current, current - 1, Ordering::SeqCst, Ordering::Relaxed)
                .is_ok()
            {
                return current;
            }
        }
    }

    fn compare_and_swap(&self, expected: u64, new: u64) -> Result<u64, u64> {
        match self
            .value
            .compare_exchange(expected, new, Ordering::SeqCst, Ordering::SeqCst)
        {
            Ok(prev) => Ok(prev),
            Err(actual) => Err(actual),
        }
    }

    fn load(&self) -> u64 {
        self.value.load(Ordering::SeqCst)
    }

    fn reset(&self) -> u64 {
        self.value.swap(0, Ordering::SeqCst)
    }
}

impl std::fmt::Debug for AtomicCounter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AtomicCounter")
            .field("value", &self.load())
            .finish()
    }
}

// ============================================================================
// Model -- sequential counter
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
struct CounterModel {
    value: u64,
}

impl CounterModel {
    fn new() -> Self {
        CounterModel { value: 0 }
    }

    fn increment(&mut self) -> u64 {
        let prev = self.value;
        self.value += 1;
        prev
    }

    fn decrement(&mut self) -> u64 {
        let prev = self.value;
        if self.value > 0 {
            self.value -= 1;
        }
        prev
    }

    fn compare_and_swap(&mut self, expected: u64, new: u64) -> Result<u64, u64> {
        if self.value == expected {
            self.value = new;
            Ok(expected)
        } else {
            Err(self.value)
        }
    }

    fn load(&self) -> u64 {
        self.value
    }

    fn reset(&mut self) -> u64 {
        let prev = self.value;
        self.value = 0;
        prev
    }
}

// ============================================================================
// Actions -- with auto-derived bridges
// ============================================================================

#[proptest_lockstep::lockstep_actions(state = CounterModel)]
pub mod counter {
    // Returns the previous value. Bridge: Transparent<u64>
    #[action(real_return = "u64")]
    pub struct Increment;

    // Returns the previous value (0 if already 0). Bridge: Transparent<u64>
    #[action(real_return = "u64")]
    pub struct Decrement;

    // CAS: Ok(prev) on success, Err(actual) on failure.
    // Bridge: ResultBridge<Transparent<u64>, Transparent<u64>>
    #[action(real_return = "Result<u64, u64>")]
    pub struct CompareAndSwap {
        pub expected: u64,
        pub new_value: u64,
    }

    // Bridge: Transparent<u64>
    #[action(real_return = "u64")]
    pub struct Load;

    // Returns the previous value. Bridge: Transparent<u64>
    #[action(real_return = "u64")]
    pub struct Reset;
}

// ============================================================================
// Interpreters
// ============================================================================

#[derive(Debug, Clone)]
struct CounterLockstep;

impl counter::CounterModelInterp for CounterLockstep {
    type State = CounterModel;

    fn increment(s: &mut CounterModel, _: &counter::Increment, _: &TypedEnv) -> u64 {
        s.increment()
    }

    fn decrement(s: &mut CounterModel, _: &counter::Decrement, _: &TypedEnv) -> u64 {
        s.decrement()
    }

    fn compare_and_swap(
        s: &mut CounterModel,
        a: &counter::CompareAndSwap,
        _: &TypedEnv,
    ) -> Result<u64, u64> {
        s.compare_and_swap(a.expected, a.new_value)
    }

    fn load(s: &mut CounterModel, _: &counter::Load, _: &TypedEnv) -> u64 {
        s.load()
    }

    fn reset(s: &mut CounterModel, _: &counter::Reset, _: &TypedEnv) -> u64 {
        s.reset()
    }
}

impl counter::CounterSutInterp for CounterLockstep {
    type Sut = AtomicCounter;

    fn increment(s: &mut AtomicCounter, _: &counter::Increment, _: &TypedEnv) -> u64 {
        s.increment()
    }

    fn decrement(s: &mut AtomicCounter, _: &counter::Decrement, _: &TypedEnv) -> u64 {
        s.decrement()
    }

    fn compare_and_swap(
        s: &mut AtomicCounter,
        a: &counter::CompareAndSwap,
        _: &TypedEnv,
    ) -> Result<u64, u64> {
        s.compare_and_swap(a.expected, a.new_value)
    }

    fn load(s: &mut AtomicCounter, _: &counter::Load, _: &TypedEnv) -> u64 {
        s.load()
    }

    fn reset(s: &mut AtomicCounter, _: &counter::Reset, _: &TypedEnv) -> u64 {
        s.reset()
    }
}

// ============================================================================
// LockstepModel
// ============================================================================

impl LockstepModel for CounterLockstep {
    type ModelState = CounterModel;
    type Sut = AtomicCounter;

    fn init_model() -> CounterModel {
        CounterModel::new()
    }
    fn init_sut() -> AtomicCounter {
        AtomicCounter::new()
    }

    fn gen_action(state: &CounterModel, _env: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        let current = state.value;

        let mut strats: Vec<BoxedStrategy<Box<dyn AnyAction>>> = vec![
            // Always allow increment and load
            Just(counter::increment(counter::Increment)).boxed(),
            Just(counter::load(counter::Load)).boxed(),
        ];

        // Decrement is interesting when counter > 0
        if current > 0 {
            strats.push(Just(counter::decrement(counter::Decrement)).boxed());
            strats.push(Just(counter::reset(counter::Reset)).boxed());
        }

        // CAS with the current value (should succeed) or a wrong value (should fail)
        strats.push(
            (0u64..=current + 2, 0u64..20)
                .prop_map(|(exp, new)| {
                    counter::compare_and_swap(counter::CompareAndSwap {
                        expected: exp,
                        new_value: new,
                    })
                })
                .boxed(),
        );

        proptest::strategy::Union::new(strats).boxed()
    }

    fn step_model(
        state: &mut CounterModel,
        action: &dyn AnyAction,
        env: &TypedEnv,
    ) -> Box<dyn Any> {
        counter::dispatch_model::<CounterLockstep>(state, action, env)
    }

    fn step_sut(
        sut: &mut AtomicCounter,
        action: &dyn AnyAction,
        env: &TypedEnv,
    ) -> Box<dyn Any> {
        counter::dispatch_sut::<CounterLockstep>(sut, action, env)
    }
}

// ============================================================================
// ConcurrentLockstepModel
// ============================================================================

#[cfg(feature = "concurrent")]
impl proptest_lockstep::concurrent::ConcurrentLockstepModel for CounterLockstep {
    fn step_sut_send(
        sut: &mut AtomicCounter,
        action: &dyn AnyAction,
        env: &TypedEnv,
    ) -> Box<dyn Any + Send> {
        counter::dispatch_sut_send::<CounterLockstep>(sut, action, env)
    }
}

fn main() {
    println!("Run with `cargo test --example concurrent_counter`");
    println!("  or `cargo test --example concurrent_counter --features concurrent`");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Sequential lockstep test: verify the atomic counter matches
    /// the u64 model under sequential operations.
    #[test]
    fn lockstep_counter() {
        proptest_lockstep::runner::run_lockstep_test::<CounterLockstep>(1..50);
    }
}

#[cfg(all(test, feature = "concurrent"))]
mod concurrent_tests {
    use super::*;
    use proptest_lockstep::concurrent::{
        lockstep_concurrent, lockstep_concurrent_with_check, lockstep_linearizable,
        ConcurrentConfig, SplitStrategy,
    };

    /// Crash-absence: concurrent increment/decrement/CAS doesn't panic.
    #[test]
    fn concurrent_counter_crash_absence() {
        lockstep_concurrent::<CounterLockstep>(ConcurrentConfig {
            iterations: 100,
            prefix_len: 5,
            branch_len: 4,
            branch_count: 2,
            split_strategy: SplitStrategy::RoundRobin,
            ..Default::default()
        });
    }

    /// Final-state check: after concurrent operations, the counter
    /// value is non-negative (can't underflow with saturating decrement).
    #[test]
    fn concurrent_counter_final_check() {
        lockstep_concurrent_with_check::<CounterLockstep, _>(
            ConcurrentConfig {
                iterations: 100,
                prefix_len: 3,
                branch_len: 5,
                branch_count: 2,
                split_strategy: SplitStrategy::Random { seed: 42 },
                ..Default::default()
            },
            |sut: &AtomicCounter| {
                // Value should be loadable without panic
                let _ = sut.load();
            },
        );
    }

    /// Linearizability: every concurrent interleaving of atomic
    /// operations is consistent with some sequential ordering.
    #[test]
    fn concurrent_counter_linearizable() {
        lockstep_linearizable::<CounterLockstep>(ConcurrentConfig {
            iterations: 50,
            prefix_len: 3,
            branch_len: 3,
            branch_count: 2,
            split_strategy: SplitStrategy::RoundRobin,
            ..Default::default()
        });
    }

    /// ConflictMaximizing: model-guided scheduling places conflicting
    /// operations (increment vs decrement on the same counter) on
    /// different branches.
    #[test]
    fn concurrent_counter_conflict_maximizing() {
        lockstep_linearizable::<CounterLockstep>(ConcurrentConfig {
            iterations: 50,
            prefix_len: 3,
            branch_len: 4,
            branch_count: 2,
            split_strategy: SplitStrategy::ConflictMaximizing,
            ..Default::default()
        });
    }
}
