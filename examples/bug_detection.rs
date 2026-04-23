#![allow(dead_code)]
//! Bug detection demonstrations.
//!
//! This example contains **intentionally buggy** implementations of
//! concurrent data structures and demonstrates that the lockstep
//! framework catches each bug. Each test is expected to FAIL --
//! the `#[should_panic]` attribute confirms the framework detects
//! the bug.
//!
//! Bug patterns demonstrated:
//! 1. **Off-by-one in pop**: stack returns wrong element
//! 2. **Stale cached length**: `len()` returns incorrect count
//! 3. **Lost update in CAS**: counter loses increments
//! 4. **Wrong eviction order**: LRU cache evicts the wrong entry
//!
//! These are realistic bug patterns that occur in production code.
//! The lockstep framework catches them all via bridge mismatch.
//!
//! Run with: `cargo test --example bug_detection`

use std::any::Any;
use std::collections::{HashMap, VecDeque};

use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;

// ============================================================================
// Bug 1: Off-by-one in stack pop
//
// A stack where pop returns the SECOND element instead of the top.
// This simulates an off-by-one indexing bug.
// ============================================================================

#[derive(Debug)]
struct BuggyStack {
    items: Vec<i32>,
}

impl BuggyStack {
    fn new() -> Self { BuggyStack { items: Vec::new() } }

    fn push(&mut self, v: i32) { self.items.push(v); }

    fn pop(&mut self) -> Option<i32> {
        if self.items.len() >= 2 {
            // BUG: removes second-to-last instead of last
            Some(self.items.remove(self.items.len() - 2))
        } else {
            self.items.pop()
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct StackModel { items: Vec<i32> }

#[proptest_lockstep::lockstep_actions(state = StackModel)]
mod buggy_stack_actions {
    #[action(real_return = "()")]
    pub struct Push { pub value: i32 }

    #[action(real_return = "Option<i32>")]
    pub struct Pop;
}

#[derive(Debug, Clone)]
struct BuggyStackLockstep;

impl buggy_stack_actions::BuggyStackActionsModelInterp for BuggyStackLockstep {
    type State = StackModel;
    fn push(s: &mut StackModel, a: &buggy_stack_actions::Push, _: &TypedEnv) {
        s.items.push(a.value);
    }
    fn pop(s: &mut StackModel, _: &buggy_stack_actions::Pop, _: &TypedEnv) -> Option<i32> {
        s.items.pop()
    }
}

impl buggy_stack_actions::BuggyStackActionsSutInterp for BuggyStackLockstep {
    type Sut = BuggyStack;
    fn push(s: &mut BuggyStack, a: &buggy_stack_actions::Push, _: &TypedEnv) {
        s.push(a.value);
    }
    fn pop(s: &mut BuggyStack, _: &buggy_stack_actions::Pop, _: &TypedEnv) -> Option<i32> {
        s.pop()
    }
}

impl LockstepModel for BuggyStackLockstep {
    type ModelState = StackModel;
    type Sut = BuggyStack;
    fn init_model() -> StackModel { StackModel { items: Vec::new() } }
    fn init_sut() -> BuggyStack { BuggyStack::new() }
    fn gen_action(_: &StackModel, _: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        prop_oneof![
            (0i32..10).prop_map(|v| buggy_stack_actions::push(buggy_stack_actions::Push { value: v })),
            Just(buggy_stack_actions::pop(buggy_stack_actions::Pop)),
        ].boxed()
    }
    fn step_model(s: &mut StackModel, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        buggy_stack_actions::dispatch_model::<BuggyStackLockstep>(s, a, e)
    }
    fn step_sut(s: &mut BuggyStack, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        buggy_stack_actions::dispatch_sut::<BuggyStackLockstep>(s, a, e)
    }
}

// ============================================================================
// Bug 2: Stale cached length
//
// A queue where len() uses a cached counter that sometimes gets out
// of sync with the actual data. This is a realistic bug pattern in
// concurrent data structures where a size counter is updated
// non-atomically relative to the data modification.
// ============================================================================

#[derive(Debug)]
struct BuggyQueue {
    data: VecDeque<i32>,
    cached_len: usize,
}

impl BuggyQueue {
    fn new() -> Self { BuggyQueue { data: VecDeque::new(), cached_len: 0 } }

    fn enqueue(&mut self, v: i32) {
        self.data.push_back(v);
        self.cached_len += 1;
    }

    fn dequeue(&mut self) -> Option<i32> {
        let result = self.data.pop_front();
        if result.is_some() {
            // BUG: only update cached_len 2/3 of the time
            if self.cached_len % 3 != 1 {
                self.cached_len -= 1;
            }
            // else: "forgot" to decrement -- cached_len is now stale
        }
        result
    }

    fn len(&self) -> usize {
        self.cached_len // Returns potentially stale length!
    }
}

#[derive(Debug, Clone, PartialEq)]
struct QueueModel { data: VecDeque<i32> }

#[proptest_lockstep::lockstep_actions(state = QueueModel)]
mod buggy_queue_actions {
    #[action(real_return = "()")]
    pub struct Enqueue { pub value: i32 }

    #[action(real_return = "Option<i32>")]
    pub struct Dequeue;

    #[action(real_return = "usize")]
    pub struct Len;
}

#[derive(Debug, Clone)]
struct BuggyQueueLockstep;

impl buggy_queue_actions::BuggyQueueActionsModelInterp for BuggyQueueLockstep {
    type State = QueueModel;
    fn enqueue(s: &mut QueueModel, a: &buggy_queue_actions::Enqueue, _: &TypedEnv) {
        s.data.push_back(a.value);
    }
    fn dequeue(s: &mut QueueModel, _: &buggy_queue_actions::Dequeue, _: &TypedEnv) -> Option<i32> {
        s.data.pop_front()
    }
    fn len(s: &mut QueueModel, _: &buggy_queue_actions::Len, _: &TypedEnv) -> usize {
        s.data.len()
    }
}

impl buggy_queue_actions::BuggyQueueActionsSutInterp for BuggyQueueLockstep {
    type Sut = BuggyQueue;
    fn enqueue(s: &mut BuggyQueue, a: &buggy_queue_actions::Enqueue, _: &TypedEnv) {
        s.enqueue(a.value);
    }
    fn dequeue(s: &mut BuggyQueue, _: &buggy_queue_actions::Dequeue, _: &TypedEnv) -> Option<i32> {
        s.dequeue()
    }
    fn len(s: &mut BuggyQueue, _: &buggy_queue_actions::Len, _: &TypedEnv) -> usize {
        s.len()
    }
}

impl LockstepModel for BuggyQueueLockstep {
    type ModelState = QueueModel;
    type Sut = BuggyQueue;
    fn init_model() -> QueueModel { QueueModel { data: VecDeque::new() } }
    fn init_sut() -> BuggyQueue { BuggyQueue::new() }
    fn gen_action(state: &QueueModel, _: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        let mut strats: Vec<BoxedStrategy<Box<dyn AnyAction>>> = vec![
            (0i32..10).prop_map(|v| buggy_queue_actions::enqueue(buggy_queue_actions::Enqueue { value: v })).boxed(),
            Just(buggy_queue_actions::len(buggy_queue_actions::Len)).boxed(),
        ];
        if !state.data.is_empty() {
            strats.push(Just(buggy_queue_actions::dequeue(buggy_queue_actions::Dequeue)).boxed());
        }
        proptest::strategy::Union::new(strats).boxed()
    }
    fn step_model(s: &mut QueueModel, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        buggy_queue_actions::dispatch_model::<BuggyQueueLockstep>(s, a, e)
    }
    fn step_sut(s: &mut BuggyQueue, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        buggy_queue_actions::dispatch_sut::<BuggyQueueLockstep>(s, a, e)
    }
}

// ============================================================================
// Bug 3: Wrong eviction in LRU cache
//
// An LRU cache that evicts the MOST recently used entry instead of
// the LEAST recently used. This simulates a common confusion between
// front/back of the eviction queue.
// ============================================================================

#[derive(Debug)]
struct BuggyLru {
    map: HashMap<String, String>,
    order: VecDeque<String>,
    capacity: usize,
}

impl BuggyLru {
    fn new(capacity: usize) -> Self {
        BuggyLru { map: HashMap::new(), order: VecDeque::new(), capacity }
    }

    fn put(&mut self, key: &str, value: &str) -> Option<String> {
        if self.map.contains_key(key) {
            self.order.retain(|k| k != key);
            self.order.push_back(key.to_string());
            return self.map.insert(key.into(), value.into());
        }

        if self.map.len() >= self.capacity {
            // BUG: evicts from the BACK (most recent) instead of FRONT (least recent)
            if let Some(evicted) = self.order.pop_back() {
                self.map.remove(&evicted);
            }
        }

        self.order.push_back(key.to_string());
        self.map.insert(key.into(), value.into())
    }

    fn get(&mut self, key: &str) -> Option<String> {
        if self.map.contains_key(key) {
            self.order.retain(|k| k != key);
            self.order.push_back(key.to_string());
            self.map.get(key).cloned()
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct LruModel {
    map: HashMap<String, String>,
    order: VecDeque<String>,
    capacity: usize,
}

impl LruModel {
    fn new(capacity: usize) -> Self {
        LruModel { map: HashMap::new(), order: VecDeque::new(), capacity }
    }
}

#[proptest_lockstep::lockstep_actions(state = LruModel)]
mod buggy_lru_actions {
    #[action(real_return = "Option<String>")]
    pub struct Put { pub key: String, pub value: String }

    #[action(real_return = "Option<String>")]
    pub struct Get { pub key: String }
}

#[derive(Debug, Clone)]
struct BuggyLruLockstep;

impl buggy_lru_actions::BuggyLruActionsModelInterp for BuggyLruLockstep {
    type State = LruModel;
    fn put(s: &mut LruModel, a: &buggy_lru_actions::Put, _: &TypedEnv) -> Option<String> {
        if s.map.contains_key(&a.key) {
            s.order.retain(|k| k != &a.key);
            s.order.push_back(a.key.clone());
            return s.map.insert(a.key.clone(), a.value.clone());
        }
        if s.map.len() >= s.capacity {
            // Model: correct LRU eviction (from front)
            if let Some(evicted) = s.order.pop_front() {
                s.map.remove(&evicted);
            }
        }
        s.order.push_back(a.key.clone());
        s.map.insert(a.key.clone(), a.value.clone())
    }
    fn get(s: &mut LruModel, a: &buggy_lru_actions::Get, _: &TypedEnv) -> Option<String> {
        if s.map.contains_key(&a.key) {
            s.order.retain(|k| k != &a.key);
            s.order.push_back(a.key.clone());
            s.map.get(&a.key).cloned()
        } else {
            None
        }
    }
}

impl buggy_lru_actions::BuggyLruActionsSutInterp for BuggyLruLockstep {
    type Sut = BuggyLru;
    fn put(s: &mut BuggyLru, a: &buggy_lru_actions::Put, _: &TypedEnv) -> Option<String> {
        s.put(&a.key, &a.value)
    }
    fn get(s: &mut BuggyLru, a: &buggy_lru_actions::Get, _: &TypedEnv) -> Option<String> {
        s.get(&a.key)
    }
}

impl LockstepModel for BuggyLruLockstep {
    type ModelState = LruModel;
    type Sut = BuggyLru;
    fn init_model() -> LruModel { LruModel::new(2) }
    fn init_sut() -> BuggyLru { BuggyLru::new(2) }
    fn gen_action(_: &LruModel, _: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        let keys = vec!["a", "b", "c", "d"];
        let vals = vec!["v1", "v2", "v3"];
        prop_oneof![
            (proptest::sample::select(keys.clone()), proptest::sample::select(vals))
                .prop_map(|(k, v)| buggy_lru_actions::put(buggy_lru_actions::Put {
                    key: k.to_string(), value: v.to_string()
                })),
            proptest::sample::select(keys)
                .prop_map(|k| buggy_lru_actions::get(buggy_lru_actions::Get { key: k.to_string() })),
        ].boxed()
    }
    fn step_model(s: &mut LruModel, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        buggy_lru_actions::dispatch_model::<BuggyLruLockstep>(s, a, e)
    }
    fn step_sut(s: &mut BuggyLru, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        buggy_lru_actions::dispatch_sut::<BuggyLruLockstep>(s, a, e)
    }
}

// ============================================================================
// Tests -- each should FAIL, proving the framework catches the bug
// ============================================================================

fn main() {
    println!("Run with `cargo test --example bug_detection`");
    println!("All tests use #[should_panic] -- they demonstrate bug DETECTION.");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Bug 1: Off-by-one in stack pop.
    /// The buggy stack returns the second element instead of the top
    /// when 2+ elements are present. The framework catches this
    /// immediately when pop is called after pushing 2+ values.
    #[test]
    #[should_panic(expected = "Lockstep mismatch")]
    fn catches_off_by_one_pop() {
        proptest_lockstep::runner::run_lockstep_test::<BuggyStackLockstep>(1..20);
    }

    /// Bug 2: Stale cached length.
    /// The buggy queue's len() returns a cached counter that drifts
    /// from the actual size after certain dequeue patterns. The
    /// framework catches this when len() disagrees with the model.
    #[test]
    #[should_panic(expected = "Lockstep mismatch")]
    fn catches_stale_cached_length() {
        proptest_lockstep::runner::run_lockstep_test::<BuggyQueueLockstep>(1..20);
    }

    /// Bug 3: Wrong eviction order in LRU cache.
    /// The buggy LRU evicts the most-recently-used entry instead of
    /// the least-recently-used. After filling the cache and inserting
    /// a new key, a get for the wrong key returns None vs Some.
    #[test]
    #[should_panic(expected = "Lockstep mismatch")]
    fn catches_wrong_eviction_order() {
        proptest_lockstep::runner::run_lockstep_test::<BuggyLruLockstep>(1..20);
    }
}
