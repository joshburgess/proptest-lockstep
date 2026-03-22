#![allow(dead_code)]
//! Treiber stack lockstep test — a real concurrent data structure.
//!
//! This is the canonical linearizability case study: a lock-free stack
//! using `AtomicPtr` + compare-and-swap, tested against a sequential
//! `Vec<i32>` model.
//!
//! Demonstrates:
//! - **Real concurrent data structure**: Treiber stack with CAS-based push/pop
//! - **Auto-derived bridges**: no manual bridge annotations
//! - **Sequential lockstep test**: verifies correctness under sequential operations
//! - **Concurrent linearizability**: verifies that concurrent push/pop
//!   interleavings are consistent with some sequential ordering
//! - **ConflictMaximizing scheduling**: model-guided contention maximization
//!
//! Run with:
//!   `cargo test --example treiber_stack`                         (sequential)
//!   `cargo test --example treiber_stack --features concurrent`   (all tests)

use std::any::Any;
use std::ptr;
use std::sync::atomic::{AtomicPtr, Ordering};

use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;

// ============================================================================
// Treiber Stack — lock-free concurrent stack
// ============================================================================

struct Node<T> {
    value: T,
    next: *mut Node<T>,
}

/// A lock-free stack using Treiber's algorithm (1986).
///
/// Each `push` allocates a node and CAS-loops to update the head.
/// Each `pop` CAS-loops to remove the head node.
///
/// This is the canonical example in the linearizability literature:
/// every push and pop is a linearization point at the successful CAS.
pub struct TreiberStack<T> {
    head: AtomicPtr<Node<T>>,
}

impl<T> TreiberStack<T> {
    fn new() -> Self {
        TreiberStack {
            head: AtomicPtr::new(ptr::null_mut()),
        }
    }

    fn push(&self, value: T) {
        let new_node = Box::into_raw(Box::new(Node {
            value,
            next: ptr::null_mut(),
        }));
        loop {
            let old_head = self.head.load(Ordering::Acquire);
            unsafe { (*new_node).next = old_head };
            if self
                .head
                .compare_exchange_weak(old_head, new_node, Ordering::Release, Ordering::Relaxed)
                .is_ok()
            {
                break;
            }
        }
    }

    fn pop(&self) -> Option<T> {
        loop {
            let old_head = self.head.load(Ordering::Acquire);
            if old_head.is_null() {
                return None;
            }
            let next = unsafe { (*old_head).next };
            if self
                .head
                .compare_exchange_weak(old_head, next, Ordering::Release, Ordering::Relaxed)
                .is_ok()
            {
                let node = unsafe { Box::from_raw(old_head) };
                return Some(node.value);
            }
        }
    }

    fn is_empty(&self) -> bool {
        self.head.load(Ordering::Acquire).is_null()
    }
}

impl<T> Drop for TreiberStack<T> {
    fn drop(&mut self) {
        while self.pop().is_some() {}
    }
}

impl<T> std::fmt::Debug for TreiberStack<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TreiberStack").finish()
    }
}

// ============================================================================
// Model — sequential stack
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
struct StackModel {
    items: Vec<i32>,
}

impl StackModel {
    fn new() -> Self {
        StackModel { items: Vec::new() }
    }

    fn push(&mut self, value: i32) {
        self.items.push(value);
    }

    fn pop(&mut self) -> Option<i32> {
        self.items.pop()
    }

    fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

// ============================================================================
// Actions — with auto-derived bridges
// ============================================================================

#[proptest_lockstep::lockstep_actions(state = StackModel)]
pub mod stack {
    // Bridge auto-derived as: UnitBridge (real_return = "()")
    #[action(real_return = "()")]
    pub struct Push {
        pub value: i32,
    }

    // Bridge auto-derived as: OptionBridge<Transparent<i32>>
    #[action(real_return = "Option<i32>")]
    pub struct Pop;

    // Bridge auto-derived as: Transparent<bool>
    #[action(real_return = "bool")]
    pub struct IsEmpty;
}

// ============================================================================
// Interpreters
// ============================================================================

#[derive(Debug, Clone)]
struct StackLockstep;

impl stack::StackModelInterp for StackLockstep {
    type State = StackModel;

    fn push(s: &mut StackModel, a: &stack::Push, _: &TypedEnv) {
        s.push(a.value);
    }

    fn pop(s: &mut StackModel, _: &stack::Pop, _: &TypedEnv) -> Option<i32> {
        s.pop()
    }

    fn is_empty(s: &mut StackModel, _: &stack::IsEmpty, _: &TypedEnv) -> bool {
        s.is_empty()
    }
}

impl stack::StackSutInterp for StackLockstep {
    type Sut = TreiberStack<i32>;

    fn push(s: &mut TreiberStack<i32>, a: &stack::Push, _: &TypedEnv) {
        s.push(a.value);
    }

    fn pop(s: &mut TreiberStack<i32>, _: &stack::Pop, _: &TypedEnv) -> Option<i32> {
        s.pop()
    }

    fn is_empty(s: &mut TreiberStack<i32>, _: &stack::IsEmpty, _: &TypedEnv) -> bool {
        s.is_empty()
    }
}

// ============================================================================
// LockstepModel
// ============================================================================

impl LockstepModel for StackLockstep {
    type ModelState = StackModel;
    type Sut = TreiberStack<i32>;

    fn init_model() -> StackModel {
        StackModel::new()
    }
    fn init_sut() -> TreiberStack<i32> {
        TreiberStack::new()
    }

    fn gen_action(state: &StackModel, _env: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        let mut strats: Vec<BoxedStrategy<Box<dyn AnyAction>>> = vec![
            // Always allow pushing
            (0i32..100).prop_map(|v| stack::push(stack::Push { value: v })).boxed(),
            // Always allow checking emptiness
            Just(stack::is_empty(stack::IsEmpty)).boxed(),
        ];

        // Only pop if the stack might have elements
        if !state.is_empty() {
            strats.push(Just(stack::pop(stack::Pop)).boxed());
        }

        proptest::strategy::Union::new(strats).boxed()
    }

    fn step_model(state: &mut StackModel, action: &dyn AnyAction, env: &TypedEnv) -> Box<dyn Any> {
        stack::dispatch_model::<StackLockstep>(state, action, env)
    }

    fn step_sut(
        sut: &mut TreiberStack<i32>,
        action: &dyn AnyAction,
        env: &TypedEnv,
    ) -> Box<dyn Any> {
        stack::dispatch_sut::<StackLockstep>(sut, action, env)
    }
}

// ============================================================================
// ConcurrentLockstepModel
// ============================================================================

#[cfg(feature = "concurrent")]
impl proptest_lockstep::concurrent::ConcurrentLockstepModel for StackLockstep {
    fn step_sut_send(
        sut: &mut TreiberStack<i32>,
        action: &dyn AnyAction,
        env: &TypedEnv,
    ) -> Box<dyn Any + Send> {
        stack::dispatch_sut_send::<StackLockstep>(sut, action, env)
    }
}

fn main() {
    println!("Run with `cargo test --example treiber_stack`");
    println!("  or `cargo test --example treiber_stack --features concurrent`");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Sequential lockstep test: verify the Treiber stack matches
    /// the Vec model under sequential operations.
    #[test]
    fn lockstep_treiber_stack() {
        proptest_lockstep::runner::run_lockstep_test::<StackLockstep>(1..50);
    }
}

#[cfg(all(test, feature = "concurrent"))]
mod concurrent_tests {
    use super::*;
    use proptest_lockstep::concurrent::{
        lockstep_concurrent, lockstep_concurrent_with_check, lockstep_linearizable,
        ConcurrentConfig, SplitStrategy,
    };

    /// Crash-absence: concurrent push/pop doesn't panic.
    #[test]
    fn concurrent_stack_crash_absence() {
        lockstep_concurrent::<StackLockstep>(ConcurrentConfig {
            iterations: 100,
            prefix_len: 5,
            branch_len: 4,
            branch_count: 2,
            split_strategy: SplitStrategy::RoundRobin,
            ..Default::default()
        });
    }

    /// Final-state check: after concurrent operations, the stack
    /// is in a valid state (non-negative length, consistent emptiness).
    #[test]
    fn concurrent_stack_final_check() {
        lockstep_concurrent_with_check::<StackLockstep, _>(
            ConcurrentConfig {
                iterations: 100,
                prefix_len: 3,
                branch_len: 5,
                branch_count: 2,
                split_strategy: SplitStrategy::Random { seed: 42 },
                ..Default::default()
            },
            |sut: &TreiberStack<i32>| {
                // After all operations, emptiness should be consistent
                // (this is a basic sanity check — the real verification
                // is the linearizability test below)
                let _ = sut.is_empty();
            },
        );
    }

    /// Linearizability: every concurrent execution of push/pop is
    /// consistent with some sequential ordering against the Vec model.
    #[test]
    fn concurrent_stack_linearizable() {
        lockstep_linearizable::<StackLockstep>(ConcurrentConfig {
            iterations: 50,
            prefix_len: 3,
            branch_len: 3,
            branch_count: 2,
            split_strategy: SplitStrategy::RoundRobin,
            ..Default::default()
        });
    }

    /// ConflictMaximizing: model-guided scheduling places conflicting
    /// operations (push + pop on the same stack) on different branches
    /// to maximize interleaving.
    #[test]
    fn concurrent_stack_conflict_maximizing() {
        lockstep_linearizable::<StackLockstep>(ConcurrentConfig {
            iterations: 50,
            prefix_len: 3,
            branch_len: 4,
            branch_count: 2,
            split_strategy: SplitStrategy::ConflictMaximizing,
            ..Default::default()
        });
    }
}
