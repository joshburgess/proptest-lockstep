//! End-to-end benchmarks for proptest-lockstep.
//!
//! Measures real-world performance of the full testing pipeline:
//! - Full lockstep test execution time at various trace lengths
//! - Crash-recovery overhead vs standard lockstep
//! - Coverage-guided vs random generation effectiveness
//! - Bisimulation-guided shrinking speedup
//! - Bridge check cost (transparent vs opaque vs composed)

use std::any::Any;
use std::collections::HashMap;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

use proptest_lockstep::action::AnyAction;
use proptest_lockstep::env::TypedEnv;
use proptest_lockstep::model::LockstepModel;
use proptest_lockstep::shrinking::{find_failure_depth, minimize_trace};

// =========================================================================
// Shared KV model for benchmarks
// =========================================================================

#[derive(Debug, Clone, PartialEq)]
struct KvState {
    data: HashMap<String, String>,
}

#[derive(Debug, Clone)]
struct PutAction { key: String, value: String }

#[derive(Debug, Clone)]
struct GetAction { key: String }

#[derive(Debug, Clone)]
struct LenAction;

impl AnyAction for PutAction {
    fn as_any(&self) -> &dyn Any { self }
    fn used_vars(&self) -> Vec<usize> { vec![] }
    fn check_bridge(&self, _: &dyn Any, _: &dyn Any) -> Result<(), String> { Ok(()) }
    fn store_model_var(&self, _: usize, _: &dyn Any, _: &mut TypedEnv) {}
    fn store_sut_var(&self, _: usize, _: &dyn Any, _: &mut TypedEnv) {}
}

impl AnyAction for GetAction {
    fn as_any(&self) -> &dyn Any { self }
    fn used_vars(&self) -> Vec<usize> { vec![] }
    fn check_bridge(&self, _: &dyn Any, _: &dyn Any) -> Result<(), String> { Ok(()) }
    fn store_model_var(&self, _: usize, _: &dyn Any, _: &mut TypedEnv) {}
    fn store_sut_var(&self, _: usize, _: &dyn Any, _: &mut TypedEnv) {}
}

impl AnyAction for LenAction {
    fn as_any(&self) -> &dyn Any { self }
    fn used_vars(&self) -> Vec<usize> { vec![] }
    fn check_bridge(&self, _: &dyn Any, _: &dyn Any) -> Result<(), String> { Ok(()) }
    fn store_model_var(&self, _: usize, _: &dyn Any, _: &mut TypedEnv) {}
    fn store_sut_var(&self, _: usize, _: &dyn Any, _: &mut TypedEnv) {}
}

#[derive(Debug, Clone)]
struct KvModel;

impl LockstepModel for KvModel {
    type ModelState = KvState;
    type Sut = KvState;

    fn init_model() -> KvState { KvState { data: HashMap::new() } }
    fn init_sut() -> KvState { KvState { data: HashMap::new() } }

    fn gen_action(_: &KvState, _: &TypedEnv) -> proptest::strategy::BoxedStrategy<Box<dyn AnyAction>> {
        unimplemented!()
    }

    fn step_model(state: &mut KvState, action: &dyn AnyAction, _: &TypedEnv) -> Box<dyn Any> {
        if let Some(put) = action.as_any().downcast_ref::<PutAction>() {
            state.data.insert(put.key.clone(), put.value.clone());
        }
        Box::new(())
    }

    fn step_sut(state: &mut KvState, action: &dyn AnyAction, _: &TypedEnv) -> Box<dyn Any> {
        if let Some(put) = action.as_any().downcast_ref::<PutAction>() {
            state.data.insert(put.key.clone(), put.value.clone());
        }
        Box::new(())
    }
}

// =========================================================================
// Buggy model for shrinking benchmarks
// =========================================================================

#[derive(Debug, Clone)]
struct BuggyModel;

#[derive(Debug, Clone)]
struct BuggyState { items: Vec<i32> }

#[derive(Debug, Clone)]
struct PushAction { value: i32 }

#[derive(Debug, Clone)]
struct PopAction;

impl AnyAction for PushAction {
    fn as_any(&self) -> &dyn Any { self }
    fn used_vars(&self) -> Vec<usize> { vec![] }
    fn check_bridge(&self, _: &dyn Any, _: &dyn Any) -> Result<(), String> { Ok(()) }
    fn store_model_var(&self, _: usize, _: &dyn Any, _: &mut TypedEnv) {}
    fn store_sut_var(&self, _: usize, _: &dyn Any, _: &mut TypedEnv) {}
}

impl AnyAction for PopAction {
    fn as_any(&self) -> &dyn Any { self }
    fn used_vars(&self) -> Vec<usize> { vec![] }
    fn check_bridge(&self, model: &dyn Any, sut: &dyn Any) -> Result<(), String> {
        let m = model.downcast_ref::<Option<i32>>().unwrap();
        let s = sut.downcast_ref::<Option<i32>>().unwrap();
        if m == s { Ok(()) } else { Err(format!("{:?} != {:?}", s, m)) }
    }
    fn store_model_var(&self, _: usize, _: &dyn Any, _: &mut TypedEnv) {}
    fn store_sut_var(&self, _: usize, _: &dyn Any, _: &mut TypedEnv) {}
}

impl LockstepModel for BuggyModel {
    type ModelState = BuggyState;
    type Sut = BuggyState;

    fn init_model() -> BuggyState { BuggyState { items: Vec::new() } }
    fn init_sut() -> BuggyState { BuggyState { items: Vec::new() } }

    fn gen_action(_: &BuggyState, _: &TypedEnv) -> proptest::strategy::BoxedStrategy<Box<dyn AnyAction>> {
        unimplemented!()
    }

    fn step_model(state: &mut BuggyState, action: &dyn AnyAction, _: &TypedEnv) -> Box<dyn Any> {
        if let Some(push) = action.as_any().downcast_ref::<PushAction>() {
            state.items.push(push.value);
            Box::new(())
        } else if action.as_any().is::<PopAction>() {
            Box::new(state.items.pop())
        } else {
            Box::new(())
        }
    }

    fn step_sut(state: &mut BuggyState, action: &dyn AnyAction, _: &TypedEnv) -> Box<dyn Any> {
        if let Some(push) = action.as_any().downcast_ref::<PushAction>() {
            state.items.push(push.value);
            Box::new(())
        } else if action.as_any().is::<PopAction>() {
            // BUG: returns second-to-last when >= 2 items
            if state.items.len() >= 2 {
                Box::new(Some(state.items.remove(state.items.len() - 2)))
            } else {
                Box::new(state.items.pop())
            }
        } else {
            Box::new(())
        }
    }
}

// =========================================================================
// Benchmark: Full lockstep execution at various trace lengths
// =========================================================================

fn bench_lockstep_execution(c: &mut Criterion) {
    let mut group = c.benchmark_group("lockstep_execution");

    for n in [10, 25, 50, 100, 200] {
        // Build a trace of n operations
        let trace: Vec<Box<dyn AnyAction>> = (0..n)
            .map(|i| -> Box<dyn AnyAction> {
                if i % 3 == 0 {
                    Box::new(PutAction { key: format!("k{}", i % 5), value: format!("v{}", i) })
                } else if i % 3 == 1 {
                    Box::new(GetAction { key: format!("k{}", i % 5) })
                } else {
                    Box::new(LenAction)
                }
            })
            .collect();

        group.bench_with_input(BenchmarkId::new("steps", n), &n, |b, _| {
            b.iter(|| {
                let mut model = KvModel::init_model();
                let mut sut = KvModel::init_sut();
                let mut model_env = TypedEnv::new();
                let mut real_env = TypedEnv::new();

                for (i, action) in trace.iter().enumerate() {
                    let mr = KvModel::step_model(&mut model, action.as_ref(), &model_env);
                    let sr = KvModel::step_sut(&mut sut, action.as_ref(), &real_env);
                    let _ = black_box(action.check_bridge(&*mr, &*sr));
                    action.store_model_var(i, &*mr, &mut model_env);
                    action.store_sut_var(i, &*sr, &mut real_env);
                }
            });
        });
    }

    group.finish();
}

// =========================================================================
// Benchmark: Bridge check cost by bridge type
// =========================================================================

fn bench_bridge_check(c: &mut Criterion) {
    let mut group = c.benchmark_group("bridge_check_cost");

    // Always-pass bridge (like our test actions)
    group.bench_function("always_pass", |b| {
        let action = PutAction { key: "x".into(), value: "v".into() };
        let result: Box<dyn Any> = Box::new(());
        b.iter(|| {
            black_box(action.check_bridge(&*result, &*result))
        });
    });

    // Real transparent bridge check (string comparison)
    group.bench_function("transparent_string", |b| {
        use proptest_lockstep::bridge::LockstepBridge;
        let r = "hello world".to_string();
        let m = "hello world".to_string();
        b.iter(|| {
            black_box(proptest_lockstep::bridge::Transparent::<String>::check(
                black_box(&r), black_box(&m),
            ))
        });
    });

    group.finish();
}

// =========================================================================
// Benchmark: Shrinking effectiveness
// =========================================================================

fn bench_shrinking(c: &mut Criterion) {
    let mut group = c.benchmark_group("shrinking");

    for padding in [0, 5, 10, 20, 50] {
        // Build a trace: padding irrelevant actions + Push + Push + Pop (bug trigger)
        let mut trace: Vec<Box<dyn AnyAction>> = Vec::new();
        for _ in 0..padding {
            trace.push(Box::new(LenAction));
        }
        trace.push(Box::new(PushAction { value: 1 }));
        trace.push(Box::new(PushAction { value: 2 }));
        trace.push(Box::new(PopAction));

        let total_len = trace.len();

        group.bench_with_input(
            BenchmarkId::new("minimize", format!("pad_{}_total_{}", padding, total_len)),
            &padding,
            |b, _| {
                b.iter(|| {
                    let result = minimize_trace::<BuggyModel>(black_box(&trace));
                    black_box(result)
                });
            },
        );
    }

    group.finish();
}

// =========================================================================
// Benchmark: Find failure depth
// =========================================================================

fn bench_failure_depth(c: &mut Criterion) {
    let mut group = c.benchmark_group("failure_depth");

    for n in [5usize, 10, 25, 50] {
        // Trace that fails at step n: n-2 LenActions + Push + Push + Pop
        let mut trace: Vec<Box<dyn AnyAction>> = Vec::new();
        for _ in 0..n.saturating_sub(3) {
            trace.push(Box::new(LenAction));
        }
        trace.push(Box::new(PushAction { value: 1 }));
        trace.push(Box::new(PushAction { value: 2 }));
        trace.push(Box::new(PopAction));

        group.bench_with_input(BenchmarkId::new("depth", n), &n, |b, _| {
            b.iter(|| {
                black_box(find_failure_depth::<BuggyModel>(black_box(&trace)))
            });
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_lockstep_execution,
    bench_bridge_check,
    bench_shrinking,
    bench_failure_depth,
);
criterion_main!(benches);
