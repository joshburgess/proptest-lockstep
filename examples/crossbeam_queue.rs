#![allow(dead_code)]
//! Crossbeam queue lockstep test -- testing a real crate from crates.io.
//!
//! Tests `crossbeam_queue::ArrayQueue` (bounded lock-free MPMC queue)
//! and `crossbeam_queue::SegQueue` (unbounded lock-free MPMC queue)
//! against sequential `VecDeque` models.
//!
//! This is a **real-world case study**: crossbeam-queue has ~50M downloads
//! and is one of the most widely-used concurrent data structure crates in
//! the Rust ecosystem. Testing it with lockstep + linearizability checking
//! demonstrates that the framework scales to production crates.
//!
//! Run with:
//!   `cargo test --example crossbeam_queue`                         (sequential)
//!   `cargo test --example crossbeam_queue --features concurrent`   (all tests)

use std::any::Any;
use std::collections::VecDeque;

use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;

// ============================================================================
// ArrayQueue -- bounded lock-free MPMC queue
// ============================================================================

// Model for ArrayQueue: bounded VecDeque
#[derive(Debug, Clone, PartialEq)]
struct ArrayQueueModel {
    buffer: VecDeque<i32>,
    capacity: usize,
}

impl ArrayQueueModel {
    fn new(capacity: usize) -> Self {
        ArrayQueueModel {
            buffer: VecDeque::with_capacity(capacity),
            capacity,
        }
    }

    fn push(&mut self, value: i32) -> Result<(), i32> {
        if self.buffer.len() >= self.capacity {
            Err(value)
        } else {
            self.buffer.push_back(value);
            Ok(())
        }
    }

    fn force_push(&mut self, value: i32) -> Option<i32> {
        if self.buffer.len() >= self.capacity {
            let evicted = self.buffer.pop_front();
            self.buffer.push_back(value);
            evicted
        } else {
            self.buffer.push_back(value);
            None
        }
    }

    fn pop(&mut self) -> Option<i32> {
        self.buffer.pop_front()
    }

    fn len(&self) -> usize {
        self.buffer.len()
    }

    fn is_empty(&self) -> bool {
        self.buffer.is_empty()
    }

    fn is_full(&self) -> bool {
        self.buffer.len() >= self.capacity
    }
}

// Actions for ArrayQueue
#[proptest_lockstep::lockstep_actions(state = ArrayQueueModel)]
pub mod aq {
    // push returns Result<(), T> -- Ok if enqueued, Err(value) if full.
    // Bridge: ResultBridge<UnitBridge, Transparent<i32>>
    #[action(real_return = "Result<(), i32>")]
    pub struct Push {
        pub value: i32,
    }

    // force_push returns Option<T> -- Some(evicted) if queue was full.
    // Bridge: OptionBridge<Transparent<i32>>
    #[action(real_return = "Option<i32>")]
    pub struct ForcePush {
        pub value: i32,
    }

    // Bridge: OptionBridge<Transparent<i32>>
    #[action(real_return = "Option<i32>")]
    pub struct Pop;

    // Bridge: Transparent<usize>
    #[action(real_return = "usize")]
    pub struct Len;

    // Bridge: Transparent<bool>
    #[action(real_return = "bool")]
    pub struct IsEmpty;

    // Bridge: Transparent<bool>
    #[action(real_return = "bool")]
    pub struct IsFull;
}

#[derive(Debug, Clone)]
struct ArrayQueueLockstep;

const AQ_CAPACITY: usize = 4;

impl aq::AqModelInterp for ArrayQueueLockstep {
    type State = ArrayQueueModel;

    fn push(s: &mut ArrayQueueModel, a: &aq::Push, _: &TypedEnv) -> Result<(), i32> {
        s.push(a.value)
    }
    fn force_push(s: &mut ArrayQueueModel, a: &aq::ForcePush, _: &TypedEnv) -> Option<i32> {
        s.force_push(a.value)
    }
    fn pop(s: &mut ArrayQueueModel, _: &aq::Pop, _: &TypedEnv) -> Option<i32> {
        s.pop()
    }
    fn len(s: &mut ArrayQueueModel, _: &aq::Len, _: &TypedEnv) -> usize {
        s.len()
    }
    fn is_empty(s: &mut ArrayQueueModel, _: &aq::IsEmpty, _: &TypedEnv) -> bool {
        s.is_empty()
    }
    fn is_full(s: &mut ArrayQueueModel, _: &aq::IsFull, _: &TypedEnv) -> bool {
        s.is_full()
    }
}

impl aq::AqSutInterp for ArrayQueueLockstep {
    type Sut = crossbeam_queue::ArrayQueue<i32>;

    fn push(s: &mut crossbeam_queue::ArrayQueue<i32>, a: &aq::Push, _: &TypedEnv) -> Result<(), i32> {
        s.push(a.value)
    }
    fn force_push(s: &mut crossbeam_queue::ArrayQueue<i32>, a: &aq::ForcePush, _: &TypedEnv) -> Option<i32> {
        s.force_push(a.value)
    }
    fn pop(s: &mut crossbeam_queue::ArrayQueue<i32>, _: &aq::Pop, _: &TypedEnv) -> Option<i32> {
        s.pop()
    }
    fn len(s: &mut crossbeam_queue::ArrayQueue<i32>, _: &aq::Len, _: &TypedEnv) -> usize {
        s.len()
    }
    fn is_empty(s: &mut crossbeam_queue::ArrayQueue<i32>, _: &aq::IsEmpty, _: &TypedEnv) -> bool {
        s.is_empty()
    }
    fn is_full(s: &mut crossbeam_queue::ArrayQueue<i32>, _: &aq::IsFull, _: &TypedEnv) -> bool {
        s.is_full()
    }
}

impl LockstepModel for ArrayQueueLockstep {
    type ModelState = ArrayQueueModel;
    type Sut = crossbeam_queue::ArrayQueue<i32>;

    fn init_model() -> ArrayQueueModel {
        ArrayQueueModel::new(AQ_CAPACITY)
    }
    fn init_sut() -> crossbeam_queue::ArrayQueue<i32> {
        crossbeam_queue::ArrayQueue::new(AQ_CAPACITY)
    }

    fn gen_action(state: &ArrayQueueModel, _env: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        let mut strats: Vec<BoxedStrategy<Box<dyn AnyAction>>> = vec![
            (0i32..100).prop_map(|v| aq::push(aq::Push { value: v })).boxed(),
            (0i32..100).prop_map(|v| aq::force_push(aq::ForcePush { value: v })).boxed(),
            Just(aq::pop(aq::Pop)).boxed(),
            Just(aq::len(aq::Len)).boxed(),
            Just(aq::is_empty(aq::IsEmpty)).boxed(),
            Just(aq::is_full(aq::IsFull)).boxed(),
        ];

        if !state.is_empty() {
            // Extra pop weight when queue has items
            strats.push(Just(aq::pop(aq::Pop)).boxed());
        }

        proptest::strategy::Union::new(strats).boxed()
    }

    fn step_model(state: &mut ArrayQueueModel, action: &dyn AnyAction, env: &TypedEnv) -> Box<dyn Any> {
        aq::dispatch_model::<ArrayQueueLockstep>(state, action, env)
    }

    fn step_sut(sut: &mut crossbeam_queue::ArrayQueue<i32>, action: &dyn AnyAction, env: &TypedEnv) -> Box<dyn Any> {
        aq::dispatch_sut::<ArrayQueueLockstep>(sut, action, env)
    }
}

#[cfg(feature = "concurrent")]
impl proptest_lockstep::concurrent::ConcurrentLockstepModel for ArrayQueueLockstep {
    fn step_sut_send(
        sut: &mut crossbeam_queue::ArrayQueue<i32>,
        action: &dyn AnyAction,
        env: &TypedEnv,
    ) -> Box<dyn Any + Send> {
        aq::dispatch_sut_send::<ArrayQueueLockstep>(sut, action, env)
    }
}

// ============================================================================
// SegQueue -- unbounded lock-free MPMC queue
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
struct SegQueueModel {
    buffer: VecDeque<i32>,
}

impl SegQueueModel {
    fn new() -> Self {
        SegQueueModel {
            buffer: VecDeque::new(),
        }
    }
}

#[proptest_lockstep::lockstep_actions(state = SegQueueModel)]
pub mod sq {
    // SegQueue::push never fails (unbounded). Returns ().
    #[action(real_return = "()")]
    pub struct Push {
        pub value: i32,
    }

    // Bridge: OptionBridge<Transparent<i32>>
    #[action(real_return = "Option<i32>")]
    pub struct Pop;

    // Bridge: Transparent<usize>
    #[action(real_return = "usize")]
    pub struct Len;

    // Bridge: Transparent<bool>
    #[action(real_return = "bool")]
    pub struct IsEmpty;
}

#[derive(Debug, Clone)]
struct SegQueueLockstep;

impl sq::SqModelInterp for SegQueueLockstep {
    type State = SegQueueModel;

    fn push(s: &mut SegQueueModel, a: &sq::Push, _: &TypedEnv) {
        s.buffer.push_back(a.value);
    }
    fn pop(s: &mut SegQueueModel, _: &sq::Pop, _: &TypedEnv) -> Option<i32> {
        s.buffer.pop_front()
    }
    fn len(s: &mut SegQueueModel, _: &sq::Len, _: &TypedEnv) -> usize {
        s.buffer.len()
    }
    fn is_empty(s: &mut SegQueueModel, _: &sq::IsEmpty, _: &TypedEnv) -> bool {
        s.buffer.is_empty()
    }
}

impl sq::SqSutInterp for SegQueueLockstep {
    type Sut = crossbeam_queue::SegQueue<i32>;

    fn push(s: &mut crossbeam_queue::SegQueue<i32>, a: &sq::Push, _: &TypedEnv) {
        s.push(a.value);
    }
    fn pop(s: &mut crossbeam_queue::SegQueue<i32>, _: &sq::Pop, _: &TypedEnv) -> Option<i32> {
        s.pop()
    }
    fn len(s: &mut crossbeam_queue::SegQueue<i32>, _: &sq::Len, _: &TypedEnv) -> usize {
        s.len()
    }
    fn is_empty(s: &mut crossbeam_queue::SegQueue<i32>, _: &sq::IsEmpty, _: &TypedEnv) -> bool {
        s.is_empty()
    }
}

impl LockstepModel for SegQueueLockstep {
    type ModelState = SegQueueModel;
    type Sut = crossbeam_queue::SegQueue<i32>;

    fn init_model() -> SegQueueModel {
        SegQueueModel::new()
    }
    fn init_sut() -> crossbeam_queue::SegQueue<i32> {
        crossbeam_queue::SegQueue::new()
    }

    fn gen_action(state: &SegQueueModel, _env: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        let mut strats: Vec<BoxedStrategy<Box<dyn AnyAction>>> = vec![
            (0i32..100).prop_map(|v| sq::push(sq::Push { value: v })).boxed(),
            Just(sq::pop(sq::Pop)).boxed(),
            Just(sq::len(sq::Len)).boxed(),
            Just(sq::is_empty(sq::IsEmpty)).boxed(),
        ];

        if !state.buffer.is_empty() {
            strats.push(Just(sq::pop(sq::Pop)).boxed());
        }

        proptest::strategy::Union::new(strats).boxed()
    }

    fn step_model(state: &mut SegQueueModel, action: &dyn AnyAction, env: &TypedEnv) -> Box<dyn Any> {
        sq::dispatch_model::<SegQueueLockstep>(state, action, env)
    }

    fn step_sut(sut: &mut crossbeam_queue::SegQueue<i32>, action: &dyn AnyAction, env: &TypedEnv) -> Box<dyn Any> {
        sq::dispatch_sut::<SegQueueLockstep>(sut, action, env)
    }
}

#[cfg(feature = "concurrent")]
impl proptest_lockstep::concurrent::ConcurrentLockstepModel for SegQueueLockstep {
    fn step_sut_send(
        sut: &mut crossbeam_queue::SegQueue<i32>,
        action: &dyn AnyAction,
        env: &TypedEnv,
    ) -> Box<dyn Any + Send> {
        sq::dispatch_sut_send::<SegQueueLockstep>(sut, action, env)
    }
}

fn main() {
    println!("Run with `cargo test --example crossbeam_queue`");
    println!("  or `cargo test --example crossbeam_queue --features concurrent`");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Sequential lockstep: ArrayQueue matches VecDeque model.
    #[test]
    fn lockstep_array_queue() {
        proptest_lockstep::runner::run_lockstep_test::<ArrayQueueLockstep>(1..50);
    }

    /// Sequential lockstep: SegQueue matches VecDeque model.
    #[test]
    fn lockstep_seg_queue() {
        proptest_lockstep::runner::run_lockstep_test::<SegQueueLockstep>(1..50);
    }
}

#[cfg(all(test, feature = "concurrent"))]
mod concurrent_tests {
    use super::*;
    use proptest_lockstep::concurrent::{
        lockstep_concurrent, lockstep_concurrent_with_check, lockstep_linearizable,
        ConcurrentConfig, SplitStrategy,
    };

    // -- ArrayQueue concurrent tests --

    #[test]
    fn array_queue_crash_absence() {
        lockstep_concurrent::<ArrayQueueLockstep>(ConcurrentConfig {
            iterations: 100,
            prefix_len: 5,
            branch_len: 4,
            branch_count: 2,
            split_strategy: SplitStrategy::RoundRobin,
            ..Default::default()
        });
    }

    #[test]
    fn array_queue_final_check() {
        lockstep_concurrent_with_check::<ArrayQueueLockstep, _>(
            ConcurrentConfig {
                iterations: 100,
                prefix_len: 3,
                branch_len: 5,
                branch_count: 2,
                split_strategy: SplitStrategy::Random { seed: 42 },
                ..Default::default()
            },
            |sut: &crossbeam_queue::ArrayQueue<i32>| {
                assert!(sut.len() <= AQ_CAPACITY);
                assert_eq!(sut.is_empty(), sut.len() == 0);
                assert_eq!(sut.is_full(), sut.len() == AQ_CAPACITY);
            },
        );
    }

    #[test]
    fn array_queue_linearizable() {
        lockstep_linearizable::<ArrayQueueLockstep>(ConcurrentConfig {
            iterations: 50,
            prefix_len: 3,
            branch_len: 3,
            branch_count: 2,
            split_strategy: SplitStrategy::RoundRobin,
            ..Default::default()
        });
    }

    #[test]
    fn array_queue_conflict_maximizing() {
        lockstep_linearizable::<ArrayQueueLockstep>(ConcurrentConfig {
            iterations: 50,
            prefix_len: 3,
            branch_len: 4,
            branch_count: 2,
            split_strategy: SplitStrategy::ConflictMaximizing,
            ..Default::default()
        });
    }

    // -- SegQueue concurrent tests --

    #[test]
    fn seg_queue_crash_absence() {
        lockstep_concurrent::<SegQueueLockstep>(ConcurrentConfig {
            iterations: 100,
            prefix_len: 5,
            branch_len: 4,
            branch_count: 2,
            split_strategy: SplitStrategy::RoundRobin,
            ..Default::default()
        });
    }

    #[test]
    fn seg_queue_linearizable() {
        lockstep_linearizable::<SegQueueLockstep>(ConcurrentConfig {
            iterations: 50,
            prefix_len: 3,
            branch_len: 3,
            branch_count: 2,
            split_strategy: SplitStrategy::RoundRobin,
            ..Default::default()
        });
    }

    #[test]
    fn seg_queue_conflict_maximizing() {
        lockstep_linearizable::<SegQueueLockstep>(ConcurrentConfig {
            iterations: 50,
            prefix_len: 3,
            branch_len: 4,
            branch_count: 2,
            split_strategy: SplitStrategy::ConflictMaximizing,
            ..Default::default()
        });
    }
}
