#![allow(dead_code)]
//! Bounded concurrent channel lockstep test.
//!
//! Tests a bounded MPMC (multi-producer multi-consumer) channel against
//! a sequential `VecDeque` model with capacity. This is a common real-world
//! concurrency primitive -- bounded channels are used in actor systems,
//! work-stealing schedulers, and pipeline architectures.
//!
//! Demonstrates:
//! - **Bounded data structure**: capacity-limited channel with backpressure
//! - **Rich result types**: `send` returns `Result<(), SendError>` to
//!   signal a full channel
//! - **Auto-derived bridges**: including for custom error types
//! - **Concurrent linearizability**: verifies that concurrent send/recv
//!   interleavings are consistent with some sequential ordering
//!
//! Run with:
//!   `cargo test --example bounded_channel`                         (sequential)
//!   `cargo test --example bounded_channel --features concurrent`   (all tests)

use std::any::Any;
use std::collections::VecDeque;
use std::sync::Mutex;

use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;

// ============================================================================
// Bounded Channel -- real concurrent data structure
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
pub enum ChannelError {
    Full,
    Empty,
}

/// A bounded MPMC channel backed by a `Mutex<VecDeque>`.
///
/// This is a realistic concurrent primitive: multiple threads can
/// send and receive concurrently, with the mutex serializing access.
/// The capacity limit creates interesting interactions between
/// producers and consumers.
pub struct BoundedChannel<T> {
    buffer: Mutex<VecDeque<T>>,
    capacity: usize,
}

impl<T> BoundedChannel<T> {
    fn new(capacity: usize) -> Self {
        BoundedChannel {
            buffer: Mutex::new(VecDeque::with_capacity(capacity)),
            capacity,
        }
    }

    fn send(&self, value: T) -> Result<(), ChannelError> {
        let mut buf = self.buffer.lock().unwrap();
        if buf.len() >= self.capacity {
            Err(ChannelError::Full)
        } else {
            buf.push_back(value);
            Ok(())
        }
    }

    fn try_recv(&self) -> Result<T, ChannelError> {
        let mut buf = self.buffer.lock().unwrap();
        buf.pop_front().ok_or(ChannelError::Empty)
    }

    fn len(&self) -> usize {
        self.buffer.lock().unwrap().len()
    }

    fn is_full(&self) -> bool {
        self.buffer.lock().unwrap().len() >= self.capacity
    }

    fn is_empty(&self) -> bool {
        self.buffer.lock().unwrap().is_empty()
    }
}

impl<T> std::fmt::Debug for BoundedChannel<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BoundedChannel")
            .field("capacity", &self.capacity)
            .field("len", &self.len())
            .finish()
    }
}

// ============================================================================
// Model -- sequential bounded queue
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
struct ChannelModel {
    buffer: VecDeque<i32>,
    capacity: usize,
}

impl ChannelModel {
    fn new(capacity: usize) -> Self {
        ChannelModel {
            buffer: VecDeque::with_capacity(capacity),
            capacity,
        }
    }

    fn send(&mut self, value: i32) -> Result<(), ChannelError> {
        if self.buffer.len() >= self.capacity {
            Err(ChannelError::Full)
        } else {
            self.buffer.push_back(value);
            Ok(())
        }
    }

    fn try_recv(&mut self) -> Result<i32, ChannelError> {
        self.buffer.pop_front().ok_or(ChannelError::Empty)
    }

    fn len(&self) -> usize {
        self.buffer.len()
    }

    fn is_full(&self) -> bool {
        self.buffer.len() >= self.capacity
    }

    fn is_empty(&self) -> bool {
        self.buffer.is_empty()
    }
}

// ============================================================================
// Actions -- with auto-derived bridges
// ============================================================================

#[proptest_lockstep::lockstep_actions(state = ChannelModel)]
pub mod chan {
    // Bridge auto-derived as: ResultBridge<UnitBridge, Transparent<ChannelError>>
    #[action(real_return = "Result<(), ChannelError>")]
    pub struct Enqueue {
        pub value: i32,
    }

    // Bridge auto-derived as: ResultBridge<Transparent<i32>, Transparent<ChannelError>>
    #[action(real_return = "Result<i32, ChannelError>")]
    pub struct TryRecv;

    // Bridge auto-derived as: Transparent<usize>
    #[action(real_return = "usize")]
    pub struct Len;

    // Bridge auto-derived as: Transparent<bool>
    #[action(real_return = "bool")]
    pub struct IsFull;

    // Bridge auto-derived as: Transparent<bool>
    #[action(real_return = "bool")]
    pub struct IsEmpty;
}

// ============================================================================
// Interpreters
// ============================================================================

#[derive(Debug, Clone)]
struct ChannelLockstep;

const CHANNEL_CAPACITY: usize = 4;

impl chan::ChanModelInterp for ChannelLockstep {
    type State = ChannelModel;

    fn enqueue(s: &mut ChannelModel, a: &chan::Enqueue, _: &TypedEnv) -> Result<(), ChannelError> {
        s.send(a.value)
    }

    fn try_recv(s: &mut ChannelModel, _: &chan::TryRecv, _: &TypedEnv) -> Result<i32, ChannelError> {
        s.try_recv()
    }

    fn len(s: &mut ChannelModel, _: &chan::Len, _: &TypedEnv) -> usize {
        s.len()
    }

    fn is_full(s: &mut ChannelModel, _: &chan::IsFull, _: &TypedEnv) -> bool {
        s.is_full()
    }

    fn is_empty(s: &mut ChannelModel, _: &chan::IsEmpty, _: &TypedEnv) -> bool {
        s.is_empty()
    }
}

impl chan::ChanSutInterp for ChannelLockstep {
    type Sut = BoundedChannel<i32>;

    fn enqueue(
        s: &mut BoundedChannel<i32>,
        a: &chan::Enqueue,
        _: &TypedEnv,
    ) -> Result<(), ChannelError> {
        s.send(a.value)
    }

    fn try_recv(
        s: &mut BoundedChannel<i32>,
        _: &chan::TryRecv,
        _: &TypedEnv,
    ) -> Result<i32, ChannelError> {
        s.try_recv()
    }

    fn len(s: &mut BoundedChannel<i32>, _: &chan::Len, _: &TypedEnv) -> usize {
        s.len()
    }

    fn is_full(s: &mut BoundedChannel<i32>, _: &chan::IsFull, _: &TypedEnv) -> bool {
        s.is_full()
    }

    fn is_empty(s: &mut BoundedChannel<i32>, _: &chan::IsEmpty, _: &TypedEnv) -> bool {
        s.is_empty()
    }
}

// ============================================================================
// LockstepModel
// ============================================================================

impl LockstepModel for ChannelLockstep {
    type ModelState = ChannelModel;
    type Sut = BoundedChannel<i32>;

    fn init_model() -> ChannelModel {
        ChannelModel::new(CHANNEL_CAPACITY)
    }
    fn init_sut() -> BoundedChannel<i32> {
        BoundedChannel::new(CHANNEL_CAPACITY)
    }

    fn gen_action(state: &ChannelModel, _env: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        let mut strats: Vec<BoxedStrategy<Box<dyn AnyAction>>> = vec![
            // Always allow sending (may return Full error)
            (0i32..100)
                .prop_map(|v| chan::enqueue(chan::Enqueue { value: v }))
                .boxed(),
            // Always allow receiving (may return Empty error)
            Just(chan::try_recv(chan::TryRecv)).boxed(),
            // Query operations
            Just(chan::len(chan::Len)).boxed(),
            Just(chan::is_full(chan::IsFull)).boxed(),
            Just(chan::is_empty(chan::IsEmpty)).boxed(),
        ];

        // Bias toward send/recv when the channel has interesting state
        if !state.is_empty() && !state.is_full() {
            // Extra weight for recv when there are items
            strats.push(Just(chan::try_recv(chan::TryRecv)).boxed());
        }

        proptest::strategy::Union::new(strats).boxed()
    }

    fn step_model(
        state: &mut ChannelModel,
        action: &dyn AnyAction,
        env: &TypedEnv,
    ) -> Box<dyn Any> {
        chan::dispatch_model::<ChannelLockstep>(state, action, env)
    }

    fn step_sut(
        sut: &mut BoundedChannel<i32>,
        action: &dyn AnyAction,
        env: &TypedEnv,
    ) -> Box<dyn Any> {
        chan::dispatch_sut::<ChannelLockstep>(sut, action, env)
    }
}

// ============================================================================
// ConcurrentLockstepModel
// ============================================================================

#[cfg(feature = "concurrent")]
impl proptest_lockstep::concurrent::ConcurrentLockstepModel for ChannelLockstep {
    fn step_sut_send(
        sut: &mut BoundedChannel<i32>,
        action: &dyn AnyAction,
        env: &TypedEnv,
    ) -> Box<dyn Any + Send> {
        chan::dispatch_sut_send::<ChannelLockstep>(sut, action, env)
    }
}

fn main() {
    println!("Run with `cargo test --example bounded_channel`");
    println!("  or `cargo test --example bounded_channel --features concurrent`");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Sequential lockstep test: verify the bounded channel matches
    /// the VecDeque model under sequential operations.
    #[test]
    fn lockstep_bounded_channel() {
        proptest_lockstep::runner::run_lockstep_test::<ChannelLockstep>(1..50);
    }
}

#[cfg(all(test, feature = "concurrent"))]
mod concurrent_tests {
    use super::*;
    use proptest_lockstep::concurrent::{
        lockstep_concurrent, lockstep_concurrent_with_check, lockstep_linearizable,
        ConcurrentConfig, SplitStrategy,
    };

    /// Crash-absence: concurrent send/recv doesn't panic.
    #[test]
    fn concurrent_channel_crash_absence() {
        lockstep_concurrent::<ChannelLockstep>(ConcurrentConfig {
            iterations: 100,
            prefix_len: 5,
            branch_len: 4,
            branch_count: 2,
            split_strategy: SplitStrategy::RoundRobin,
            ..Default::default()
        });
    }

    /// Final-state check: after concurrent operations, the channel
    /// length is within capacity bounds.
    #[test]
    fn concurrent_channel_final_check() {
        lockstep_concurrent_with_check::<ChannelLockstep, _>(
            ConcurrentConfig {
                iterations: 100,
                prefix_len: 3,
                branch_len: 5,
                branch_count: 2,
                split_strategy: SplitStrategy::Random { seed: 7 },
                ..Default::default()
            },
            |sut: &BoundedChannel<i32>| {
                assert!(sut.len() <= CHANNEL_CAPACITY);
                assert_eq!(sut.is_empty(), sut.len() == 0);
                assert_eq!(sut.is_full(), sut.len() >= CHANNEL_CAPACITY);
            },
        );
    }

    /// Linearizability: every concurrent send/recv interleaving is
    /// consistent with some sequential ordering.
    #[test]
    fn concurrent_channel_linearizable() {
        lockstep_linearizable::<ChannelLockstep>(ConcurrentConfig {
            iterations: 50,
            prefix_len: 3,
            branch_len: 3,
            branch_count: 2,
            split_strategy: SplitStrategy::RoundRobin,
            ..Default::default()
        });
    }

    /// ConflictMaximizing: model-guided scheduling places conflicting
    /// operations (send + recv) on different branches.
    #[test]
    fn concurrent_channel_conflict_maximizing() {
        lockstep_linearizable::<ChannelLockstep>(ConcurrentConfig {
            iterations: 50,
            prefix_len: 3,
            branch_len: 4,
            branch_count: 2,
            split_strategy: SplitStrategy::ConflictMaximizing,
            ..Default::default()
        });
    }
}
