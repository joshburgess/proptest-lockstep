//! Benchmarks for the linearizability checker and DPOR.
//!
//! Measures:
//! - DPOR pruning effectiveness (ratio of pruned interleavings)
//! - DPOR vs brute-force performance
//! - Scaling behavior with operation count
//! - Commutativity detection overhead

use std::any::Any;
use std::collections::HashMap;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

use proptest_lockstep::action::AnyAction;
use proptest_lockstep::concurrent::{
    check_linearizability, operations_commute, BudgetExceeded, LinearizabilityStats, OpRecord,
};
use proptest_lockstep::env::TypedEnv;
use proptest_lockstep::model::LockstepModel;

// =========================================================================
// KV model for benchmarks
//
// Uses a HashMap model for commutativity detection (PartialEq on state),
// but the bridge always passes -- this lets us benchmark DPOR pruning
// independently of bridge check cost.
// =========================================================================

#[derive(Debug, Clone, PartialEq)]
struct KvState {
    data: HashMap<String, String>,
}

/// A write action -- mutates model state. Bridge always passes.
#[derive(Debug, Clone)]
struct Put {
    key: String,
    value: String,
}

/// A read action -- doesn't mutate state. Bridge always passes.
#[derive(Debug, Clone)]
struct Get {
    key: String,
}

impl AnyAction for Put {
    fn as_any(&self) -> &dyn Any { self }
    fn used_vars(&self) -> Vec<usize> { vec![] }
    fn check_bridge(&self, _: &dyn Any, _: &dyn Any) -> Result<(), String> { Ok(()) }
    fn store_model_var(&self, _: usize, _: &dyn Any, _: &mut TypedEnv) {}
    fn store_sut_var(&self, _: usize, _: &dyn Any, _: &mut TypedEnv) {}
}

impl AnyAction for Get {
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
    type Sut = ();

    fn init_model() -> KvState {
        KvState { data: HashMap::new() }
    }
    fn init_sut() -> () {}

    fn gen_action(
        _: &KvState,
        _: &TypedEnv,
    ) -> proptest::strategy::BoxedStrategy<Box<dyn AnyAction>> {
        unimplemented!()
    }

    fn step_model(state: &mut KvState, action: &dyn AnyAction, _: &TypedEnv) -> Box<dyn Any> {
        if let Some(put) = action.as_any().downcast_ref::<Put>() {
            state.data.insert(put.key.clone(), put.value.clone());
        }
        // Get doesn't modify state; return () for both
        Box::new(())
    }

    fn step_sut(_: &mut (), _: &dyn AnyAction, _: &TypedEnv) -> Box<dyn Any> {
        Box::new(())
    }
}

// =========================================================================
// Workload generators
// =========================================================================

/// All operations on disjoint keys (maximal commutativity).
fn disjoint_workload(n: usize) -> Vec<Vec<OpRecord>> {
    let branch1: Vec<OpRecord> = (0..n)
        .map(|i| OpRecord {
            action: Box::new(Put {
                key: format!("a{i}"),
                value: format!("v{i}"),
            }),
            result: Box::new(None::<String>),
            var_id: i,
        })
        .collect();
    let branch2: Vec<OpRecord> = (0..n)
        .map(|i| OpRecord {
            action: Box::new(Put {
                key: format!("b{i}"),
                value: format!("v{i}"),
            }),
            result: Box::new(None::<String>),
            var_id: n + i,
        })
        .collect();
    vec![branch1, branch2]
}

/// All operations write to the same key -- they don't commute, but
/// linearization succeeds because the bridge always passes (both
/// orderings produce valid Put results: the previous value).
/// Uses pre-populated state so results are predictable.
fn conflicting_workload(n: usize) -> Vec<Vec<OpRecord>> {
    // Reads on distinct keys that don't exist -- all return None,
    // which is what the model also returns regardless of order.
    // Operations touch the same conceptual resource (Get on keys
    // that overlap between branches) but since Get is idempotent,
    // every ordering is valid. However, operations on overlapping
    // keys don't commute in the model when mixed with writes.
    //
    // For a clean non-commuting benchmark, use writes to the same
    // key where the recorded result is None (first write).
    let branch1: Vec<OpRecord> = (0..n)
        .map(|i| OpRecord {
            action: Box::new(Put {
                key: "shared".into(),
                value: format!("a{i}"),
            }),
            result: Box::new(None::<String>),
            var_id: i,
        })
        .collect();
    // Second branch: reads from keys that don't exist → None
    let branch2: Vec<OpRecord> = (0..n)
        .map(|i| OpRecord {
            action: Box::new(Get {
                key: format!("nonexistent{i}"),
            }),
            result: Box::new(None::<String>),
            var_id: n + i,
        })
        .collect();
    vec![branch1, branch2]
}

/// Mixed: some operations commute, some don't.
fn mixed_workload(n: usize) -> Vec<Vec<OpRecord>> {
    let branch1: Vec<OpRecord> = (0..n)
        .map(|i| OpRecord {
            action: if i % 2 == 0 {
                Box::new(Put {
                    key: "shared".into(),
                    value: format!("a{i}"),
                }) as Box<dyn AnyAction>
            } else {
                Box::new(Get {
                    key: format!("unique_a{i}"),
                })
            },
            result: Box::new(None::<String>),
            var_id: i,
        })
        .collect();
    let branch2: Vec<OpRecord> = (0..n)
        .map(|i| OpRecord {
            action: if i % 2 == 0 {
                Box::new(Put {
                    key: "shared".into(),
                    value: format!("b{i}"),
                }) as Box<dyn AnyAction>
            } else {
                Box::new(Get {
                    key: format!("unique_b{i}"),
                })
            },
            result: Box::new(None::<String>),
            var_id: n + i,
        })
        .collect();
    vec![branch1, branch2]
}

// =========================================================================
// Benchmarks
// =========================================================================

fn bench_dpor_vs_brute_force(c: &mut Criterion) {
    let mut group = c.benchmark_group("dpor_vs_brute_force");

    for n in [2, 3, 4, 5] {
        let branches = disjoint_workload(n);
        let model = KvModel::init_model();
        let env = TypedEnv::new();

        group.bench_with_input(BenchmarkId::new("dpor", n), &n, |b, _| {
            b.iter(|| {
                let mut stats = LinearizabilityStats::default();
                check_linearizability::<KvModel>(
                    black_box(&model),
                    &env,
                    &branches,
                    1_000_000,
                    BudgetExceeded::Fail,
                    &mut stats,
                    true,
                )
                .unwrap();
                stats
            });
        });

        group.bench_with_input(BenchmarkId::new("brute_force", n), &n, |b, _| {
            b.iter(|| {
                let mut stats = LinearizabilityStats::default();
                check_linearizability::<KvModel>(
                    black_box(&model),
                    &env,
                    &branches,
                    1_000_000,
                    BudgetExceeded::Fail,
                    &mut stats,
                    false,
                )
                .unwrap();
                stats
            });
        });
    }

    group.finish();
}

fn bench_dpor_pruning_ratio(c: &mut Criterion) {
    let mut group = c.benchmark_group("dpor_pruning_ratio");

    for n in [2, 3, 4, 5, 6] {
        // Disjoint keys: DPOR should prune heavily
        let branches = disjoint_workload(n);
        let model = KvModel::init_model();
        let env = TypedEnv::new();

        group.bench_with_input(BenchmarkId::new("disjoint", n), &n, |b, _| {
            b.iter(|| {
                let mut stats = LinearizabilityStats::default();
                check_linearizability::<KvModel>(
                    black_box(&model),
                    &env,
                    &branches,
                    1_000_000,
                    BudgetExceeded::Fail,
                    &mut stats,
                    true,
                )
                .unwrap();
                stats
            });
        });

        // Conflicting keys: DPOR can't prune much
        let branches = conflicting_workload(n);
        group.bench_with_input(BenchmarkId::new("conflicting", n), &n, |b, _| {
            b.iter(|| {
                let mut stats = LinearizabilityStats::default();
                check_linearizability::<KvModel>(
                    black_box(&model),
                    &env,
                    &branches,
                    1_000_000,
                    BudgetExceeded::Fail,
                    &mut stats,
                    true,
                )
                .unwrap();
                stats
            });
        });

        // Mixed: partial pruning
        let branches = mixed_workload(n);
        group.bench_with_input(BenchmarkId::new("mixed", n), &n, |b, _| {
            b.iter(|| {
                let mut stats = LinearizabilityStats::default();
                check_linearizability::<KvModel>(
                    black_box(&model),
                    &env,
                    &branches,
                    1_000_000,
                    BudgetExceeded::Fail,
                    &mut stats,
                    true,
                )
                .unwrap();
                stats
            });
        });
    }

    group.finish();
}

fn bench_commutativity_check(c: &mut Criterion) {
    let mut group = c.benchmark_group("commutativity_check");

    let model = KvModel::init_model();
    let env = TypedEnv::new();

    // Commuting pair (disjoint keys)
    let a = OpRecord {
        action: Box::new(Put {
            key: "x".into(),
            value: "1".into(),
        }),
        result: Box::new(None::<String>),
        var_id: 0,
    };
    let b = OpRecord {
        action: Box::new(Put {
            key: "y".into(),
            value: "2".into(),
        }),
        result: Box::new(None::<String>),
        var_id: 1,
    };

    group.bench_function("commuting_pair", |bench| {
        bench.iter(|| {
            operations_commute::<KvModel>(black_box(&model), &env, &a, &b)
        });
    });

    // Non-commuting pair (same key)
    let c_op = OpRecord {
        action: Box::new(Put {
            key: "x".into(),
            value: "1".into(),
        }),
        result: Box::new(None::<String>),
        var_id: 0,
    };
    let d = OpRecord {
        action: Box::new(Put {
            key: "x".into(),
            value: "2".into(),
        }),
        result: Box::new(None::<String>),
        var_id: 1,
    };

    group.bench_function("non_commuting_pair", |bench| {
        bench.iter(|| {
            operations_commute::<KvModel>(black_box(&model), &env, &c_op, &d)
        });
    });

    // Read-read (always commutes)
    let e = OpRecord {
        action: Box::new(Get { key: "x".into() }),
        result: Box::new(None::<String>),
        var_id: 0,
    };
    let f = OpRecord {
        action: Box::new(Get { key: "x".into() }),
        result: Box::new(None::<String>),
        var_id: 1,
    };

    group.bench_function("read_read_pair", |bench| {
        bench.iter(|| {
            operations_commute::<KvModel>(black_box(&model), &env, &e, &f)
        });
    });

    group.finish();
}

fn bench_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("linearizability_scaling");
    group.sample_size(10);

    for n in [2, 3, 4, 5, 6, 7] {
        let branches = disjoint_workload(n);
        let model = KvModel::init_model();
        let env = TypedEnv::new();

        group.bench_with_input(BenchmarkId::new("disjoint_dpor", n), &n, |b, _| {
            b.iter(|| {
                let mut stats = LinearizabilityStats::default();
                check_linearizability::<KvModel>(
                    black_box(&model),
                    &env,
                    &branches,
                    1_000_000,
                    BudgetExceeded::Warn,
                    &mut stats,
                    true,
                )
            });
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_dpor_vs_brute_force,
    bench_dpor_pruning_ratio,
    bench_commutativity_check,
    bench_scaling,
);
criterion_main!(benches);
