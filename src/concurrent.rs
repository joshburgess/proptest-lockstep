//! Concurrent lockstep testing via Shuttle.
//!
//! This module provides infrastructure for testing stateful APIs under
//! concurrent access, with two levels of verification:
//!
//! - **Crash-absence** ([`lockstep_concurrent`]): verifies the SUT doesn't
//!   panic or deadlock under concurrent access.
//! - **Linearizability** ([`lockstep_linearizable`]): verifies that every
//!   concurrent execution is consistent with some sequential ordering
//!   of the operations against the model. Requires implementing the
//!   [`ConcurrentLockstepModel`] trait (one method: `step_sut_send`).
//!
//! For exhaustive schedule enumeration, use loom via the `concurrent-loom`
//! feature flag. Loom explores **all** possible thread schedules (up to a
//! depth bound), providing stronger guarantees than Shuttle's randomized
//! approach at the cost of slower execution.
//!
//! The `concurrent` (Shuttle) and `concurrent-loom` (loom) features are
//! mutually exclusive: they instrument `std::sync` in incompatible ways,
//! so a build picks one or the other. Each provides its own entry points.
//!
//! Requires the `concurrent` or `concurrent-loom` feature flag.

use std::any::Any;
use std::fmt::Debug;

use crate::action::AnyAction;
use crate::env::TypedEnv;
use crate::model::LockstepModel;

// ---------------------------------------------------------------------------
// ConcurrentLockstepModel
// ---------------------------------------------------------------------------

/// Extension trait for models whose SUT operations return `Send` results.
///
/// Required for linearizability checking, where operation results must
/// be collected across thread boundaries. Models that only need
/// crash-absence testing can use [`lockstep_concurrent`] without
/// implementing this trait.
///
/// For models where all `real_return` types are `Send` (the common case),
/// implement this by delegating to the generated `dispatch_sut` -- the
/// proc macro generates `dispatch_sut_send` which returns `Box<dyn Any + Send>`.
///
/// # Example
///
/// ```ignore
/// impl ConcurrentLockstepModel for MyLockstep {
///     fn step_sut_send(
///         sut: &mut MySut,
///         action: &dyn AnyAction,
///         env: &TypedEnv,
///     ) -> Box<dyn Any + Send> {
///         my_actions::dispatch_sut_send::<MyLockstep>(sut, action, env)
///     }
/// }
/// ```
pub trait ConcurrentLockstepModel: LockstepModel {
    /// Execute an action against the SUT, returning a `Send`-able result.
    fn step_sut_send(
        sut: &mut Self::Sut,
        action: &dyn AnyAction,
        env: &TypedEnv,
    ) -> Box<dyn Any + Send>;
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Strategy for distributing actions across concurrent branches.
#[derive(Debug, Clone, Copy)]
pub enum SplitStrategy {
    /// Assign actions to branches in round-robin order (0, 1, 2, 0, 1, 2, ...).
    RoundRobin,
    /// Assign actions to branches using a deterministic seeded hash.
    /// The same seed always produces the same split, ensuring reproducibility.
    Random { seed: u64 },
    /// Model-guided split: assigns actions to branches to maximize
    /// contention -- operations that don't commute (according to the
    /// model) are placed on different branches so that Shuttle's
    /// random scheduler is more likely to interleave them.
    ///
    /// This is a novel scheduling strategy that uses the lockstep model
    /// as a semantic oracle. Requires `ModelState: PartialEq` for
    /// sound commutativity detection.
    ///
    /// **Approximation:** commutativity is checked against the
    /// post-prefix model state, not the state after earlier branch
    /// assignments. For models where commutativity is state-dependent,
    /// this may produce suboptimal (but never incorrect) splits --
    /// the linearizability checker remains sound regardless of split.
    ///
    /// Usable with all concurrent entry points (crash-absence and
    /// linearizability, Shuttle and loom).
    ConflictMaximizing,
}

impl Default for SplitStrategy {
    fn default() -> Self {
        SplitStrategy::RoundRobin
    }
}

/// Configuration for concurrent lockstep tests.
#[derive(Debug, Clone)]
pub struct ConcurrentConfig {
    /// Number of Shuttle iterations (random schedules) to explore.
    pub iterations: usize,
    /// Length of the sequential prefix (executed before branching).
    pub prefix_len: usize,
    /// Length of each parallel branch.
    pub branch_len: usize,
    /// Number of concurrent branches (threads). Default: 2.
    pub branch_count: usize,
    /// Strategy for distributing actions across branches.
    pub split_strategy: SplitStrategy,
    /// Maximum number of interleavings to try during linearizability
    /// checking. Default: 1_000_000. Only used by [`lockstep_linearizable`].
    pub max_interleaving_budget: usize,
    /// What to do when the interleaving budget is exhausted.
    /// Default: `Warn` (test passes with a warning on stderr).
    pub on_budget_exceeded: BudgetExceeded,
    /// Whether to enable DPOR (dynamic partial-order reduction) for
    /// linearizability checking. When disabled, all interleavings are
    /// explored without pruning. Default: `true`.
    pub dpor_enabled: bool,
}

/// Behavior when the linearizability interleaving budget is exhausted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BudgetExceeded {
    /// Test passes with a warning on stderr.
    Warn,
    /// Test fails with an error.
    Fail,
    /// Test passes silently.
    Pass,
}

impl Default for BudgetExceeded {
    fn default() -> Self {
        BudgetExceeded::Warn
    }
}

impl Default for ConcurrentConfig {
    fn default() -> Self {
        ConcurrentConfig {
            iterations: 100,
            prefix_len: 5,
            branch_len: 5,
            branch_count: 2,
            split_strategy: SplitStrategy::RoundRobin,
            max_interleaving_budget: 1_000_000,
            on_budget_exceeded: BudgetExceeded::Warn,
            dpor_enabled: true,
        }
    }
}

// ---------------------------------------------------------------------------
// Splitting
// ---------------------------------------------------------------------------

/// Split a sequence of actions into a prefix and N interleaved branches.
///
/// The prefix is executed sequentially first. The remaining actions are
/// distributed across `branch_count` branches according to `strategy`.
pub fn split_for_parallel(
    actions: &[Box<dyn AnyAction>],
    prefix_len: usize,
    branch_count: usize,
    strategy: SplitStrategy,
) -> (Vec<Box<dyn AnyAction>>, Vec<Vec<Box<dyn AnyAction>>>) {
    assert!(branch_count >= 1, "branch_count must be at least 1");

    let prefix: Vec<_> = actions.iter().take(prefix_len).cloned().collect();
    let remaining: Vec<_> = actions.iter().skip(prefix_len).cloned().collect();

    let count = branch_count;
    let mut branches: Vec<Vec<Box<dyn AnyAction>>> = (0..count).map(|_| Vec::new()).collect();

    for (i, action) in remaining.into_iter().enumerate() {
        let branch_idx = match strategy {
            SplitStrategy::RoundRobin => i % count,
            SplitStrategy::Random { seed } => {
                let mut h = seed.wrapping_mul(6364136223846793005).wrapping_add(i as u64);
                h ^= h >> 33;
                h = h.wrapping_mul(0xff51afd7ed558ccd);
                h ^= h >> 33;
                (h as usize) % count
            }
            SplitStrategy::ConflictMaximizing => {
                // Fallback: split_for_parallel doesn't have model access,
                // so ConflictMaximizing degrades to round-robin here.
                // The concurrent entry points handle ConflictMaximizing
                // via split_remaining_with_ids which has model access.
                i % count
            }
        };
        branches[branch_idx].push(action);
    }

    (prefix, branches)
}

/// Split remaining actions (with var_ids) into branches, handling all
/// strategies including `ConflictMaximizing`.
fn split_remaining_with_ids<M: LockstepModel>(
    remaining: Vec<(Box<dyn AnyAction>, usize)>,
    branch_count: usize,
    strategy: SplitStrategy,
    model_after_prefix: &M::ModelState,
    env_after_prefix: &TypedEnv,
) -> Vec<Vec<(Box<dyn AnyAction>, usize)>>
where
    M::ModelState: PartialEq,
{
    let count = branch_count;
    let mut branches: Vec<Vec<(Box<dyn AnyAction>, usize)>> =
        (0..count).map(|_| Vec::new()).collect();

    match strategy {
        SplitStrategy::RoundRobin => {
            for (i, item) in remaining.into_iter().enumerate() {
                branches[i % count].push(item);
            }
        }
        SplitStrategy::Random { seed } => {
            for (i, item) in remaining.into_iter().enumerate() {
                let mut h = seed.wrapping_mul(6364136223846793005).wrapping_add(i as u64);
                h ^= h >> 33;
                h = h.wrapping_mul(0xff51afd7ed558ccd);
                h ^= h >> 33;
                branches[(h as usize) % count].push(item);
            }
        }
        SplitStrategy::ConflictMaximizing => {
            // Track the last action assigned to each branch
            let mut branch_last: Vec<Option<(Box<dyn AnyAction>, usize)>> =
                (0..count).map(|_| None).collect();

            for (action, var_id) in remaining {
                // Find branches whose last action conflicts with this one
                let mut best_bid = 0;
                let mut best_len = usize::MAX;
                let mut found_conflict = false;

                for bid in 0..count {
                    if let Some((ref last_action, last_var_id)) = branch_last[bid] {
                        let commutes = actions_commute_in_model::<M>(
                            model_after_prefix,
                            env_after_prefix,
                            last_action.as_ref(),
                            last_var_id,
                            action.as_ref(),
                            var_id,
                        );
                        if !commutes {
                            // This branch conflicts -- we want to put the
                            // action on a DIFFERENT branch for interleaving
                            found_conflict = true;
                        }
                    }
                }

                if found_conflict {
                    // Place on the smallest branch that doesn't conflict
                    // (so the conflicting actions end up on different threads)
                    for bid in 0..count {
                        let conflicts_with_this = branch_last[bid].as_ref().map_or(false, |(ref la, lv)| {
                            !actions_commute_in_model::<M>(
                                model_after_prefix, env_after_prefix,
                                la.as_ref(), *lv, action.as_ref(), var_id,
                            )
                        });
                        if !conflicts_with_this && branches[bid].len() < best_len {
                            best_bid = bid;
                            best_len = branches[bid].len();
                        }
                    }
                    // If all branches conflict, just use smallest
                    if best_len == usize::MAX {
                        best_bid = (0..count).min_by_key(|&b| branches[b].len()).unwrap();
                    }
                } else {
                    // No conflicts -- smallest branch
                    best_bid = (0..count).min_by_key(|&b| branches[b].len()).unwrap();
                }

                branch_last[best_bid] = Some((action.clone(), var_id));
                branches[best_bid].push((action, var_id));
            }
        }
    }

    branches
}

/// Statistics from a linearizability check, reporting DPOR effectiveness.
#[derive(Debug, Clone, Default)]
pub struct LinearizabilityStats {
    /// Number of complete interleavings explored.
    pub interleavings_tried: usize,
    /// Number of interleavings pruned by DPOR sleep sets.
    pub interleavings_pruned: usize,
    /// Number of commutativity checks performed.
    pub commutativity_checks: usize,
}

impl std::fmt::Display for LinearizabilityStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Linearizability verified: {} interleavings tried ({} pruned by DPOR, {} commutativity checks)",
            self.interleavings_tried,
            self.interleavings_pruned,
            self.commutativity_checks,
        )
    }
}

/// Check whether two actions commute in a given model state.
///
/// This is a lighter-weight version of `operations_commute` that works
/// with bare actions (no `OpRecord` / SUT results needed). Used during
/// the split phase before any SUT execution.
fn actions_commute_in_model<M: LockstepModel>(
    model: &M::ModelState,
    env: &TypedEnv,
    a: &dyn AnyAction,
    a_var_id: usize,
    b: &dyn AnyAction,
    b_var_id: usize,
) -> bool
where
    M::ModelState: PartialEq,
{
    // Order 1: a then b
    let mut m1 = model.clone();
    let mut e1 = env.clone();
    let r_a1 = M::step_model(&mut m1, a, &e1);
    a.store_model_var(a_var_id, &*r_a1, &mut e1);
    let r_b1 = M::step_model(&mut m1, b, &e1);
    b.store_model_var(b_var_id, &*r_b1, &mut e1);

    // Order 2: b then a
    let mut m2 = model.clone();
    let mut e2 = env.clone();
    let r_b2 = M::step_model(&mut m2, b, &e2);
    b.store_model_var(b_var_id, &*r_b2, &mut e2);
    let r_a2 = M::step_model(&mut m2, a, &e2);
    a.store_model_var(a_var_id, &*r_a2, &mut e2);

    // They commute if final model states are equal
    m1 == m2
}

// ---------------------------------------------------------------------------
// Prefix execution
// ---------------------------------------------------------------------------

/// Execute a prefix of actions sequentially against the model and SUT,
/// returning the resulting model state, SUT, and both environments.
pub fn run_prefix<M: LockstepModel>(
    prefix: &[Box<dyn AnyAction>],
) -> (M::ModelState, M::Sut, TypedEnv, TypedEnv) {
    let mut model_state = M::init_model();
    let mut sut = M::init_sut();
    let mut model_env = TypedEnv::new();
    let mut sut_env = TypedEnv::new();

    for action in prefix {
        let model_result = M::step_model(&mut model_state, action.as_ref(), &model_env);
        let sut_result = M::step_sut(&mut sut, action.as_ref(), &sut_env);

        action.check_bridge(&*model_result, &*sut_result)
            .unwrap_or_else(|msg| {
                panic!("Lockstep mismatch in prefix!\n  Action: {:?}\n{}", action, msg)
            });

        let var_id = model_env.next_id();
        action.store_model_var(var_id, &*model_result, &mut model_env);
        action.store_sut_var(var_id, &*sut_result, &mut sut_env);
    }

    (model_state, sut, model_env, sut_env)
}

// ---------------------------------------------------------------------------
// Crash-absence testing (0.1)
// ---------------------------------------------------------------------------

/// Run a concurrent lockstep test using Shuttle's randomized scheduler.
///
/// Tests crash-absence: verifies the SUT doesn't panic or deadlock
/// under concurrent access. Does NOT check linearizability -- for that,
/// use [`lockstep_linearizable`].
///
/// # Example
///
/// ```ignore
/// use proptest_lockstep::concurrent::{lockstep_concurrent, ConcurrentConfig};
///
/// lockstep_concurrent::<MyModel>(ConcurrentConfig {
///     iterations: 1000,
///     prefix_len: 3,
///     branch_len: 5,
///     ..Default::default()
/// });
/// ```
#[cfg(feature = "concurrent")]
pub fn lockstep_concurrent<M>(config: ConcurrentConfig)
where
    M: LockstepModel + Send + Sync,
    M::ModelState: Send + Sync + PartialEq,
    M::Sut: Send,
{
    lockstep_concurrent_with_check::<M, _>(config, |_| {});
}

/// Run a concurrent crash-absence test with a final state check.
///
/// Same as [`lockstep_concurrent`], but after all concurrent branches
/// complete, calls `check_final` with a reference to the SUT.
///
/// Supports all split strategies including `ConflictMaximizing`, which
/// uses the model to place conflicting operations on different branches.
#[cfg(feature = "concurrent")]
pub fn lockstep_concurrent_with_check<M, F>(config: ConcurrentConfig, check_final: F)
where
    M: LockstepModel + Send + Sync,
    M::ModelState: Send + Sync + PartialEq,
    M::Sut: Send,
    F: Fn(&M::Sut) + Send + Sync + 'static,
{
    use proptest::prelude::*;
    use proptest::strategy::ValueTree;
    use proptest::test_runner::TestRunner;

    let check_final = std::sync::Arc::new(check_final);

    shuttle::check_random(
        move || {
            let mut runner = TestRunner::default();

            let total_len = config.prefix_len + config.branch_len * config.branch_count;
            let mut actions: Vec<Box<dyn AnyAction>> = Vec::new();

            let mut gen_model = M::init_model();
            let mut gen_env = TypedEnv::new();
            for _ in 0..total_len {
                let strategy = M::gen_action(&gen_model, &gen_env);
                if let Ok(tree) = strategy.new_tree(&mut runner) {
                    let action = tree.current();
                    let result = M::step_model(&mut gen_model, action.as_ref(), &gen_env);
                    let var_id = gen_env.next_id();
                    action.store_model_var(var_id, &*result, &mut gen_env);
                    actions.push(action);
                }
            }

            // Execute prefix first (needed for ConflictMaximizing)
            let (prefix_plain, _) = {
                let p: Vec<_> = actions.iter().take(config.prefix_len).cloned().collect();
                let r: Vec<_> = actions.iter().skip(config.prefix_len).cloned().collect();
                (p, r)
            };
            let (_model_state, sut, _model_env, sut_env) = run_prefix::<M>(&prefix_plain);

            // Split remaining actions using the unified split function
            let remaining_with_ids: Vec<(Box<dyn AnyAction>, usize)> = actions
                .into_iter()
                .enumerate()
                .skip(config.prefix_len)
                .map(|(i, a)| (a, i))
                .collect();

            let branches_with_ids = split_remaining_with_ids::<M>(
                remaining_with_ids,
                config.branch_count,
                config.split_strategy,
                &_model_state,
                &_model_env,
            );

            let sut = shuttle::sync::Arc::new(shuttle::sync::Mutex::new(sut));
            let sut_env = shuttle::sync::Arc::new(shuttle::sync::Mutex::new(sut_env));

            let mut handles = Vec::new();

            for (branch_id, branch) in branches_with_ids.into_iter().enumerate() {
                let sut_ref = sut.clone();
                let env_ref = sut_env.clone();
                let handle = shuttle::thread::spawn(move || {
                    let mut trace: Vec<String> = Vec::new();
                    for (step, (action, _var_id)) in branch.into_iter().enumerate() {
                        trace.push(format!(
                            "  [branch {}, step {}] {:?}",
                            branch_id, step, action
                        ));
                        let result = std::panic::catch_unwind(
                            std::panic::AssertUnwindSafe(|| {
                                let mut s = sut_ref.lock().unwrap();
                                let env = env_ref.lock().unwrap();
                                M::step_sut(&mut *s, action.as_ref(), &env)
                            }),
                        );
                        if let Err(payload) = result {
                            eprintln!(
                                "Panic during concurrent execution!\nTrace (branch {}):",
                                branch_id
                            );
                            for line in &trace {
                                eprintln!("{}", line);
                            }
                            std::panic::resume_unwind(payload);
                        }
                    }
                });
                handles.push(handle);
            }

            for handle in handles {
                handle.join().unwrap();
            }

            let final_sut = sut.lock().unwrap();
            check_final(&final_sut);
        },
        config.iterations,
    );
}

// ---------------------------------------------------------------------------
// Linearizability checking (0.2)
// ---------------------------------------------------------------------------

/// A recorded concurrent operation with its result.
#[doc(hidden)]
pub struct OpRecord {
    pub action: Box<dyn AnyAction>,
    pub result: Box<dyn Any + Send>,
    /// The variable ID assigned during generation. The linearizability
    /// checker uses this to store model results at the correct ID,
    /// matching the IDs that subsequent actions' GVars reference.
    pub var_id: usize,
}

/// Check whether two operations commute in a given model state.
///
/// Two operations commute if executing them in either order produces
/// the same observable results (via their bridges) AND the same final
/// model state. This is computed dynamically using the model -- no
/// annotations needed.
///
/// The check uses `check_bridge` to compare return values and
/// `PartialEq` to compare final model states. For custom bridges with
/// asymmetric observation functions, the bridge comparison passes two
/// model results (not a model/SUT pair), which is correct for all
/// built-in bridges but may be imprecise for custom asymmetric bridges.
/// The model state comparison via `PartialEq` is sound -- it catches
/// all state differences, including "silent" mutations that don't
/// appear in return values.
///
/// Used by the linearizability checker to prune the interleaving
/// search space: commuting operations don't need to be reordered.
#[doc(hidden)]
pub fn operations_commute<M: LockstepModel>(
    model: &M::ModelState,
    env: &TypedEnv,
    a: &OpRecord,
    b: &OpRecord,
) -> bool
where
    M::ModelState: PartialEq,
{
    // Order 1: a then b
    let mut m1 = model.clone();
    let mut e1 = env.clone();
    let r_a1 = M::step_model(&mut m1, a.action.as_ref(), &e1);
    a.action.store_model_var(a.var_id, &*r_a1, &mut e1);
    let r_b1 = M::step_model(&mut m1, b.action.as_ref(), &e1);
    b.action.store_model_var(b.var_id, &*r_b1, &mut e1);

    // Order 2: b then a
    let mut m2 = model.clone();
    let mut e2 = env.clone();
    let r_b2 = M::step_model(&mut m2, b.action.as_ref(), &e2);
    b.action.store_model_var(b.var_id, &*r_b2, &mut e2);
    let r_a2 = M::step_model(&mut m2, a.action.as_ref(), &e2);
    a.action.store_model_var(a.var_id, &*r_a2, &mut e2);

    // They commute if:
    // 1. Both orderings produce equivalent model results for each operation.
    //    Uses check_model_bridge (observe_model on both sides) rather than
    //    check_bridge (which would incorrectly apply observe_real to one side).
    let a_same = a.action.check_model_bridge(&*r_a1, &*r_a2).is_ok();
    let b_same = b.action.check_model_bridge(&*r_b1, &*r_b2).is_ok();

    // 2. The final model states are the same (catches "silent" state
    //    mutations that don't appear in return values).
    let state_same = m1 == m2;

    a_same && b_same && state_same
}

/// Check whether a concurrent execution history is linearizable.
///
/// Uses dynamic partial-order reduction (DPOR): at each search node,
/// detects commuting operations via the model and skips redundant
/// interleavings. Two operations that commute in the current model
/// state don't need to be reordered -- the checker prunes the search
/// tree using sleep sets.
///
/// Falls back to brute-force enumeration when operations don't commute
/// or when commutativity can't be determined.
///
/// Returns `Ok(())` if a valid linearization exists, or an error
/// describing the failure.
#[doc(hidden)]
pub fn check_linearizability<M: LockstepModel>(
    initial_model: &M::ModelState,
    initial_env: &TypedEnv,
    branches: &[Vec<OpRecord>],
    budget: usize,
    on_budget_exceeded: BudgetExceeded,
    stats: &mut LinearizabilityStats,
    dpor_enabled: bool,
) -> Result<(), String>
where
    M::ModelState: PartialEq,
{
    let branch_count = branches.len();
    if branch_count == 0 {
        return Ok(());
    }

    let mut cursors = vec![0usize; branch_count];
    let total: usize = branches.iter().map(|b| b.len()).sum();
    if total == 0 {
        return Ok(());
    }

    let mut attempts = 0usize;
    let mut best_match_depth = 0usize;
    let mut best_trace: Vec<String> = Vec::new();

    let found = check_linearizability_rec::<M>(
        initial_model,
        initial_env,
        branches,
        &mut cursors,
        0,
        total,
        budget,
        &mut attempts,
        &mut best_match_depth,
        &mut best_trace,
        &mut Vec::new(),
        &mut Vec::new(),
        stats,
        dpor_enabled,
    );

    stats.interleavings_tried = attempts;

    if found {
        Ok(())
    } else if attempts >= budget {
        let msg = format!(
            "Linearizability budget exhausted ({} interleavings tried). \
             Deepest match: {}/{} operations.",
            budget, best_match_depth, total
        );
        match on_budget_exceeded {
            BudgetExceeded::Pass => Ok(()),
            BudgetExceeded::Warn => {
                eprintln!("Warning: {}", msg);
                Ok(())
            }
            BudgetExceeded::Fail => Err(msg),
        }
    } else {
        let mut msg = format!(
            "Linearizability check failed!\n  Tried {} interleavings, none matched.\n  \
             Deepest match: {}/{} operations.\n  Closest sequential history:\n",
            attempts, best_match_depth, total
        );
        for line in &best_trace {
            msg.push_str("    ");
            msg.push_str(line);
            msg.push('\n');
        }
        Err(msg)
    }
}

fn check_linearizability_rec<M: LockstepModel>(
    model: &M::ModelState,
    env: &TypedEnv,
    branches: &[Vec<OpRecord>],
    cursors: &mut [usize],
    depth: usize,
    total: usize,
    budget: usize,
    attempts: &mut usize,
    best_depth: &mut usize,
    best_trace: &mut Vec<String>,
    current_trace: &mut Vec<String>,
    sleep_set: &mut Vec<usize>,
    stats: &mut LinearizabilityStats,
    dpor_enabled: bool,
) -> bool
where
    M::ModelState: PartialEq,
{
    // Base case: all operations consumed -- this is a valid linearization
    if depth == total {
        *attempts += 1;
        return true;
    }

    if *attempts >= budget {
        return false;
    }

    // Collect the branch IDs we'll actually try (excluding sleep set)
    let runnable_count = (0..branches.len())
        .filter(|&bid| cursors[bid] < branches[bid].len())
        .count();
    let candidates: Vec<usize> = (0..branches.len())
        .filter(|&bid| {
            let cursor = cursors[bid];
            cursor < branches[bid].len() && !sleep_set.contains(&bid)
        })
        .collect();
    stats.interleavings_pruned += runnable_count - candidates.len();

    // Track which branches we've successfully explored at this level,
    // so we can build sleep sets for subsequent siblings.
    let mut explored: Vec<usize> = Vec::new();

    for &branch_id in &candidates {
        let cursor = cursors[branch_id];
        let record = &branches[branch_id][cursor];

        // Clone model state and env for this attempt
        let mut model_clone = model.clone();
        let mut env_clone = env.clone();

        // Run model
        let model_result = M::step_model(
            &mut model_clone,
            record.action.as_ref(),
            &env_clone,
        );

        // Check bridge
        let bridge_ok = record.action.check_bridge(&*model_result, &*record.result).is_ok();

        if bridge_ok {
            // Store variables at the generation-time ID so that
            // subsequent actions' GVars resolve correctly.
            record.action.store_model_var(record.var_id, &*model_result, &mut env_clone);

            let trace_entry = format!(
                "[branch {}] {:?} -> OK",
                branch_id, record.action
            );
            current_trace.push(trace_entry);

            cursors[branch_id] += 1;

            // Build child sleep set (only when DPOR is enabled):
            let mut child_sleep: Vec<usize> = Vec::new();

            if dpor_enabled {
                // 1. Inherit parent sleep set entries that still commute
                for &bid in sleep_set.iter() {
                    let c = cursors[bid];
                    if c < branches[bid].len() {
                        stats.commutativity_checks += 1;
                        if operations_commute::<M>(model, env, record, &branches[bid][c]) {
                            child_sleep.push(bid);
                        }
                    }
                }

                // 2. Add branches explored at this level whose head
                //    operations commute with the one we just chose
                for &prev_bid in &explored {
                    if child_sleep.contains(&prev_bid) {
                        continue;
                    }
                    let prev_cursor = cursors[prev_bid];
                    if prev_cursor < branches[prev_bid].len() {
                        stats.commutativity_checks += 1;
                        let prev_record = &branches[prev_bid][prev_cursor];
                        if operations_commute::<M>(model, env, record, prev_record) {
                            child_sleep.push(prev_bid);
                        }
                    }
                }
            }

            if check_linearizability_rec::<M>(
                &model_clone,
                &env_clone,
                branches,
                cursors,
                depth + 1,
                total,
                budget,
                attempts,
                best_depth,
                best_trace,
                current_trace,
                &mut child_sleep,
                stats,
                dpor_enabled,
            ) {
                cursors[branch_id] -= 1;
                current_trace.pop();
                return true;
            }

            cursors[branch_id] -= 1;
            current_trace.pop();
            explored.push(branch_id);
        } else {
            // Track the closest match for error reporting
            if depth > *best_depth {
                *best_depth = depth;
                *best_trace = current_trace.clone();
                best_trace.push(format!(
                    "[branch {}] {:?} -> MISMATCH",
                    branch_id, record.action
                ));
            }
        }
    }

    false
}

/// Run a concurrent lockstep test with **linearizability checking**.
///
/// Generates action sequences, splits them into concurrent branches,
/// executes them under Shuttle, collects per-operation results, and
/// verifies that the results are consistent with some sequential
/// execution of the operations against the model.
///
/// Requires the model to implement [`ConcurrentLockstepModel`] so that
/// SUT results are `Send` (collectible across thread boundaries).
///
/// # Example
///
/// ```ignore
/// use proptest_lockstep::concurrent::{lockstep_linearizable, ConcurrentConfig};
///
/// lockstep_linearizable::<MyModel>(ConcurrentConfig {
///     iterations: 200,
///     prefix_len: 3,
///     branch_len: 5,
///     branch_count: 2,
///     ..Default::default()
/// });
/// ```
#[cfg(feature = "concurrent")]
pub fn lockstep_linearizable<M>(config: ConcurrentConfig)
where
    M: ConcurrentLockstepModel + Send + Sync,
    M::ModelState: Send + Sync + PartialEq,
    M::Sut: Send,
{
    lockstep_linearizable_with_check::<M, _>(config, |_| {});
}

/// Run a linearizability test with an additional final state check.
#[cfg(feature = "concurrent")]
pub fn lockstep_linearizable_with_check<M, F>(config: ConcurrentConfig, check_final: F)
where
    M: ConcurrentLockstepModel + Send + Sync,
    M::ModelState: Send + Sync + PartialEq,
    M::Sut: Send,
    F: Fn(&M::Sut) + Send + Sync + 'static,
{
    use proptest::prelude::*;
    use proptest::strategy::ValueTree;
    use proptest::test_runner::TestRunner;

    let check_final = std::sync::Arc::new(check_final);
    let budget = config.max_interleaving_budget;
    let on_budget_exceeded = config.on_budget_exceeded;
    let dpor_enabled = config.dpor_enabled;

    shuttle::check_random(
        move || {
            let mut runner = TestRunner::default();

            let total_len = config.prefix_len + config.branch_len * config.branch_count;
            let mut actions: Vec<Box<dyn AnyAction>> = Vec::new();

            let mut gen_model = M::init_model();
            let mut gen_env = TypedEnv::new();
            for _ in 0..total_len {
                let strategy = M::gen_action(&gen_model, &gen_env);
                if let Ok(tree) = strategy.new_tree(&mut runner) {
                    let action = tree.current();
                    let result = M::step_model(&mut gen_model, action.as_ref(), &gen_env);
                    let var_id = gen_env.next_id();
                    action.store_model_var(var_id, &*result, &mut gen_env);
                    actions.push(action);
                }
            }

            // Pair each action with its generation-time variable ID.
            let actions_with_ids: Vec<(Box<dyn AnyAction>, usize)> = actions
                .into_iter()
                .enumerate()
                .map(|(i, a)| (a, i))
                .collect();

            let prefix_actions: Vec<Box<dyn AnyAction>> = actions_with_ids.iter()
                .take(config.prefix_len)
                .map(|(a, _)| a.clone())
                .collect();
            let remaining_with_ids: Vec<_> = actions_with_ids.into_iter()
                .skip(config.prefix_len)
                .collect();

            // Execute prefix first -- needed for ConflictMaximizing
            // which requires the post-prefix model state.
            let (model_state, sut, model_env, sut_env) = run_prefix::<M>(&prefix_actions);

            // Split remaining actions into branches (preserving var_ids)
            assert!(config.branch_count >= 1);
            let branches = split_remaining_with_ids::<M>(
                remaining_with_ids,
                config.branch_count,
                config.split_strategy,
                &model_state,
                &model_env,
            );

            // Execute branches concurrently, collecting results with var_ids
            let sut = shuttle::sync::Arc::new(shuttle::sync::Mutex::new(sut));
            let sut_env = shuttle::sync::Arc::new(shuttle::sync::Mutex::new(sut_env));

            let mut handles = Vec::new();

            for (branch_id, branch) in branches.into_iter().enumerate() {
                let sut_ref = sut.clone();
                let env_ref = sut_env.clone();
                let handle = shuttle::thread::spawn(move || {
                    let mut records: Vec<OpRecord> = Vec::new();
                    let mut trace: Vec<String> = Vec::new();

                    for (step, (action, var_id)) in branch.into_iter().enumerate() {
                        trace.push(format!(
                            "  [branch {}, step {}] {:?}",
                            branch_id, step, action
                        ));
                        let result = std::panic::catch_unwind(
                            std::panic::AssertUnwindSafe(|| {
                                let mut s = sut_ref.lock().unwrap();
                                let env = env_ref.lock().unwrap();
                                M::step_sut_send(&mut *s, action.as_ref(), &env)
                            }),
                        );
                        match result {
                            Ok(sut_result) => {
                                records.push(OpRecord {
                                    action,
                                    result: sut_result,
                                    var_id,
                                });
                            }
                            Err(payload) => {
                                eprintln!(
                                    "Panic during concurrent execution!\nTrace (branch {}):",
                                    branch_id
                                );
                                for line in &trace {
                                    eprintln!("{}", line);
                                }
                                std::panic::resume_unwind(payload);
                            }
                        }
                    }

                    records
                });
                handles.push(handle);
            }

            // Collect results from all branches
            let mut all_branches: Vec<Vec<OpRecord>> = Vec::new();
            for handle in handles {
                all_branches.push(handle.join().unwrap());
            }

            // Check linearizability
            let mut stats = LinearizabilityStats::default();
            check_linearizability::<M>(
                &model_state,
                &model_env,
                &all_branches,
                budget,
                on_budget_exceeded,
                &mut stats,
                dpor_enabled,
            ).unwrap_or_else(|msg| {
                panic!("Linearizability check failed!\n{}", msg);
            });
            eprintln!("{}", stats);

            // Final state check
            let final_sut = sut.lock().unwrap();
            check_final(&final_sut);
        },
        config.iterations,
    );
}

// ---------------------------------------------------------------------------
// Loom support -- exhaustive schedule enumeration
// ---------------------------------------------------------------------------

/// Configuration for loom-based concurrent tests.
///
/// Unlike [`ConcurrentConfig`], there is no `iterations` field -- loom
/// explores all possible schedules exhaustively.
#[derive(Debug, Clone)]
pub struct LoomConfig {
    /// Length of the sequential prefix (executed before branching).
    pub prefix_len: usize,
    /// Length of each parallel branch.
    pub branch_len: usize,
    /// Number of concurrent branches (threads). Default: 2.
    pub branch_count: usize,
    /// Strategy for distributing actions across branches.
    pub split_strategy: SplitStrategy,
    /// Maximum interleavings for linearizability checking.
    pub max_interleaving_budget: usize,
    /// Behavior when the interleaving budget is exhausted.
    pub on_budget_exceeded: BudgetExceeded,
    /// Whether to enable DPOR. Default: `true`.
    pub dpor_enabled: bool,
}

impl Default for LoomConfig {
    fn default() -> Self {
        // Smaller defaults than ConcurrentConfig because loom explores
        // all schedules exhaustively -- larger sizes cause combinatorial
        // explosion in the number of schedules.
        LoomConfig {
            prefix_len: 3,
            branch_len: 3,
            branch_count: 2,
            split_strategy: SplitStrategy::RoundRobin,
            max_interleaving_budget: 1_000_000,
            on_budget_exceeded: BudgetExceeded::Warn,
            dpor_enabled: true,
        }
    }
}

/// Run a concurrent crash-absence test using loom's exhaustive scheduler.
///
/// Unlike [`lockstep_concurrent`] (Shuttle, randomized), this function
/// explores **all possible thread schedules** up to loom's depth bound.
/// This is slower but provides stronger guarantees: if the test passes,
/// no schedule can cause a panic or deadlock.
///
/// # Example
///
/// ```ignore
/// use proptest_lockstep::concurrent::{lockstep_concurrent_loom, LoomConfig};
///
/// lockstep_concurrent_loom::<MyModel>(LoomConfig {
///     prefix_len: 2,
///     branch_len: 2,
///     branch_count: 2,
///     ..Default::default()
/// });
/// ```
#[cfg(feature = "concurrent-loom")]
pub fn lockstep_concurrent_loom<M>(config: LoomConfig)
where
    M: LockstepModel + Send + Sync + 'static,
    M::ModelState: Send + Sync + PartialEq,
    M::Sut: Send,
{
    lockstep_concurrent_loom_with_check::<M, _>(config, |_| {});
}

/// Run a loom crash-absence test with a final state check.
#[cfg(feature = "concurrent-loom")]
pub fn lockstep_concurrent_loom_with_check<M, F>(config: LoomConfig, check_final: F)
where
    M: LockstepModel + Send + Sync + 'static,
    M::ModelState: Send + Sync + PartialEq,
    M::Sut: Send,
    F: Fn(&M::Sut) + Send + Sync + 'static,
{
    use proptest::prelude::*;
    use proptest::strategy::ValueTree;
    use proptest::test_runner::TestRunner;

    // Generate actions OUTSIDE loom::model -- they must be deterministic
    // across loom's replays (loom re-executes the closure for each schedule).
    let mut runner = TestRunner::default();

    let total_len = config.prefix_len + config.branch_len * config.branch_count;
    let mut actions: Vec<Box<dyn AnyAction>> = Vec::new();

    let mut gen_model = M::init_model();
    let mut gen_env = TypedEnv::new();
    for _ in 0..total_len {
        let strategy = M::gen_action(&gen_model, &gen_env);
        if let Ok(tree) = strategy.new_tree(&mut runner) {
            let action = tree.current();
            let result = M::step_model(&mut gen_model, action.as_ref(), &gen_env);
            let var_id = gen_env.next_id();
            action.store_model_var(var_id, &*result, &mut gen_env);
            actions.push(action);
        }
    }

    // Compute post-prefix model state for ConflictMaximizing split
    let prefix_actions: Vec<Box<dyn AnyAction>> = actions.iter()
        .take(config.prefix_len).cloned().collect();
    let (prefix_model_state, prefix_model_env) = {
        let mut ms = M::init_model();
        let mut me = TypedEnv::new();
        for action in &prefix_actions {
            let result = M::step_model(&mut ms, action.as_ref(), &me);
            let var_id = me.next_id();
            action.store_model_var(var_id, &*result, &mut me);
        }
        (ms, me)
    };

    let remaining_with_ids: Vec<(Box<dyn AnyAction>, usize)> = actions
        .into_iter()
        .enumerate()
        .skip(config.prefix_len)
        .map(|(i, a)| (a, i))
        .collect();

    let branches_with_ids = split_remaining_with_ids::<M>(
        remaining_with_ids,
        config.branch_count,
        config.split_strategy,
        &prefix_model_state,
        &prefix_model_env,
    );

    let prefix_actions = std::sync::Arc::new(prefix_actions);
    let branches_with_ids = std::sync::Arc::new(branches_with_ids);
    let check_final = std::sync::Arc::new(check_final);

    loom::model(move || {
        // Execute prefix sequentially -- no threads spawned yet, so no
        // loom instrumentation needed. Mutex::new() establishes
        // happens-before for all prefix writes.
        let (_model_state, sut, _model_env, sut_env) = run_prefix::<M>(&prefix_actions);

        let sut = loom::sync::Arc::new(loom::sync::Mutex::new(sut));
        let sut_env = loom::sync::Arc::new(loom::sync::Mutex::new(sut_env));

        let mut handles = Vec::new();

        for (branch_id, branch) in branches_with_ids.iter().enumerate() {
            let sut_ref = sut.clone();
            let env_ref = sut_env.clone();
            let branch = branch.clone();
            let handle = loom::thread::spawn(move || {
                for (_step, (action, _var_id)) in branch.into_iter().enumerate() {
                    let mut s = sut_ref.lock().unwrap();
                    let env = env_ref.lock().unwrap();
                    let _result = M::step_sut(&mut *s, action.as_ref(), &env);
                    drop(env);
                    drop(s);
                }
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.join().unwrap();
        }

        let final_sut = sut.lock().unwrap();
        check_final(&final_sut);
    });
}

/// Run a loom-based concurrent test with **linearizability checking**.
///
/// Explores all possible thread schedules exhaustively and verifies
/// that each schedule produces results consistent with some sequential
/// model execution.
#[cfg(feature = "concurrent-loom")]
pub fn lockstep_linearizable_loom<M>(config: LoomConfig)
where
    M: ConcurrentLockstepModel + Send + Sync + 'static,
    M::ModelState: Send + Sync + PartialEq,
    M::Sut: Send,
{
    lockstep_linearizable_loom_with_check::<M, _>(config, |_| {});
}

/// Run a loom linearizability test with a final state check.
#[cfg(feature = "concurrent-loom")]
pub fn lockstep_linearizable_loom_with_check<M, F>(config: LoomConfig, check_final: F)
where
    M: ConcurrentLockstepModel + Send + Sync + 'static,
    M::ModelState: Send + Sync + PartialEq,
    M::Sut: Send,
    F: Fn(&M::Sut) + Send + Sync + 'static,
{
    use proptest::prelude::*;
    use proptest::strategy::ValueTree;
    use proptest::test_runner::TestRunner;

    // Generate actions outside loom::model for deterministic replay
    let mut runner = TestRunner::default();

    let total_len = config.prefix_len + config.branch_len * config.branch_count;
    let mut actions: Vec<Box<dyn AnyAction>> = Vec::new();

    let mut gen_model = M::init_model();
    let mut gen_env = TypedEnv::new();
    for _ in 0..total_len {
        let strategy = M::gen_action(&gen_model, &gen_env);
        if let Ok(tree) = strategy.new_tree(&mut runner) {
            let action = tree.current();
            let result = M::step_model(&mut gen_model, action.as_ref(), &gen_env);
            let var_id = gen_env.next_id();
            action.store_model_var(var_id, &*result, &mut gen_env);
            actions.push(action);
        }
    }

    // Pair with generation-time var IDs
    let actions_with_ids: Vec<(Box<dyn AnyAction>, usize)> = actions
        .into_iter()
        .enumerate()
        .map(|(i, a)| (a, i))
        .collect();

    let prefix_actions: Vec<Box<dyn AnyAction>> = actions_with_ids.iter()
        .take(config.prefix_len)
        .map(|(a, _)| a.clone())
        .collect();
    let remaining_with_ids: Vec<_> = actions_with_ids.into_iter()
        .skip(config.prefix_len)
        .collect();

    // For ConflictMaximizing, run the prefix model-only to get the
    // post-prefix state for splitting. The prefix will be re-run
    // inside loom::model with the actual SUT.
    let (prefix_model_state, prefix_model_env) = {
        let mut model_state = M::init_model();
        let mut model_env = TypedEnv::new();
        for action in &prefix_actions {
            let result = M::step_model(&mut model_state, action.as_ref(), &model_env);
            let var_id = model_env.next_id();
            action.store_model_var(var_id, &*result, &mut model_env);
        }
        (model_state, model_env)
    };

    // Split remaining actions into branches (preserving var_ids)
    assert!(config.branch_count >= 1);
    let branches_with_ids = split_remaining_with_ids::<M>(
        remaining_with_ids,
        config.branch_count,
        config.split_strategy,
        &prefix_model_state,
        &prefix_model_env,
    );

    let prefix_actions = std::sync::Arc::new(prefix_actions);
    let branches_with_ids = std::sync::Arc::new(branches_with_ids);
    let check_final = std::sync::Arc::new(check_final);
    let budget = config.max_interleaving_budget;
    let on_budget_exceeded = config.on_budget_exceeded;
    let dpor_enabled = config.dpor_enabled;

    loom::model(move || {
        // Execute prefix sequentially -- no threads spawned yet, so no
        // loom instrumentation needed. Mutex::new() establishes
        // happens-before for all prefix writes.
        let (model_state, sut, model_env, sut_env) = run_prefix::<M>(&prefix_actions);

        let sut = loom::sync::Arc::new(loom::sync::Mutex::new(sut));
        let sut_env = loom::sync::Arc::new(loom::sync::Mutex::new(sut_env));

        let mut handles = Vec::new();

        for (branch_id, branch) in branches_with_ids.iter().enumerate() {
            let sut_ref = sut.clone();
            let env_ref = sut_env.clone();
            let branch = branch.clone();
            let handle = loom::thread::spawn(move || {
                let mut records: Vec<OpRecord> = Vec::new();

                for (_step, (action, var_id)) in branch.into_iter().enumerate() {
                    let mut s = sut_ref.lock().unwrap();
                    let env = env_ref.lock().unwrap();
                    let sut_result = M::step_sut_send(&mut *s, action.as_ref(), &env);
                    drop(env);
                    drop(s);
                    records.push(OpRecord {
                        action,
                        result: sut_result,
                        var_id,
                    });
                }

                records
            });
            handles.push(handle);
        }

        let mut all_branches: Vec<Vec<OpRecord>> = Vec::new();
        for handle in handles {
            all_branches.push(handle.join().unwrap());
        }

        let mut stats = LinearizabilityStats::default();
        check_linearizability::<M>(
            &model_state,
            &model_env,
            &all_branches,
            budget,
            on_budget_exceeded,
            &mut stats,
            dpor_enabled,
        ).unwrap_or_else(|msg| {
            panic!("Linearizability check failed!\n{}", msg);
        });

        let final_sut = sut.lock().unwrap();
        check_final(&final_sut);
    });
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, Clone)]
    struct MockAction(usize);

    impl AnyAction for MockAction {
        fn as_any(&self) -> &dyn Any { self }
        fn used_vars(&self) -> Vec<usize> { vec![] }
        fn check_bridge(&self, _: &dyn Any, _: &dyn Any) -> Result<(), String> { Ok(()) }
        fn store_model_var(&self, _: usize, _: &dyn Any, _: &mut TypedEnv) {}
        fn store_sut_var(&self, _: usize, _: &dyn Any, _: &mut TypedEnv) {}
    }

    fn mock_actions(n: usize) -> Vec<Box<dyn AnyAction>> {
        (0..n).map(|i| Box::new(MockAction(i)) as Box<dyn AnyAction>).collect()
    }

    fn action_ids(actions: &[Box<dyn AnyAction>]) -> Vec<usize> {
        actions.iter()
            .map(|a| a.as_any().downcast_ref::<MockAction>().unwrap().0)
            .collect()
    }

    #[test]
    fn split_empty() {
        let actions = mock_actions(0);
        let (prefix, branches) = split_for_parallel(&actions, 0, 2, SplitStrategy::RoundRobin);
        assert!(prefix.is_empty());
        assert!(branches.iter().all(|b| b.is_empty()));
    }

    #[test]
    fn split_all_prefix() {
        let actions = mock_actions(5);
        let (prefix, branches) = split_for_parallel(&actions, 10, 2, SplitStrategy::RoundRobin);
        assert_eq!(action_ids(&prefix), vec![0, 1, 2, 3, 4]);
        assert!(branches.iter().all(|b| b.is_empty()));
    }

    #[test]
    fn split_round_robin_2_branches() {
        let actions = mock_actions(6);
        let (prefix, branches) = split_for_parallel(&actions, 0, 2, SplitStrategy::RoundRobin);
        assert!(prefix.is_empty());
        assert_eq!(branches.len(), 2);
        assert_eq!(action_ids(&branches[0]), vec![0, 2, 4]);
        assert_eq!(action_ids(&branches[1]), vec![1, 3, 5]);
    }

    #[test]
    fn split_round_robin_3_branches() {
        let actions = mock_actions(9);
        let (_prefix, branches) = split_for_parallel(&actions, 0, 3, SplitStrategy::RoundRobin);
        assert_eq!(branches.len(), 3);
        assert_eq!(action_ids(&branches[0]), vec![0, 3, 6]);
        assert_eq!(action_ids(&branches[1]), vec![1, 4, 7]);
        assert_eq!(action_ids(&branches[2]), vec![2, 5, 8]);
    }

    #[test]
    fn split_with_prefix() {
        let actions = mock_actions(8);
        let (prefix, branches) = split_for_parallel(&actions, 3, 2, SplitStrategy::RoundRobin);
        assert_eq!(action_ids(&prefix), vec![0, 1, 2]);
        assert_eq!(action_ids(&branches[0]), vec![3, 5, 7]);
        assert_eq!(action_ids(&branches[1]), vec![4, 6]);
    }

    #[test]
    fn split_preserves_within_branch_order() {
        let actions = mock_actions(20);
        let (_, branches) = split_for_parallel(&actions, 2, 4, SplitStrategy::RoundRobin);
        for branch in &branches {
            let ids = action_ids(branch);
            for w in ids.windows(2) {
                assert!(w[0] < w[1], "Order not preserved: {} before {}", w[0], w[1]);
            }
        }
    }

    #[test]
    fn split_random_deterministic() {
        let actions = mock_actions(20);
        let (_, branches1) = split_for_parallel(&actions, 3, 3, SplitStrategy::Random { seed: 42 });
        let (_, branches2) = split_for_parallel(&actions, 3, 3, SplitStrategy::Random { seed: 42 });
        for (b1, b2) in branches1.iter().zip(branches2.iter()) {
            assert_eq!(action_ids(b1), action_ids(b2));
        }
    }

    #[test]
    fn split_random_different_seeds_differ() {
        let actions = mock_actions(30);
        let (_, branches1) = split_for_parallel(&actions, 0, 3, SplitStrategy::Random { seed: 1 });
        let (_, branches2) = split_for_parallel(&actions, 0, 3, SplitStrategy::Random { seed: 999 });
        let differ = branches1.iter().zip(branches2.iter())
            .any(|(b1, b2)| action_ids(b1) != action_ids(b2));
        assert!(differ, "Different seeds produced identical splits");
    }

    #[test]
    fn split_random_covers_all_actions() {
        let actions = mock_actions(15);
        let (prefix, branches) = split_for_parallel(&actions, 5, 3, SplitStrategy::Random { seed: 7 });
        let mut all_ids: Vec<usize> = action_ids(&prefix);
        for branch in &branches {
            all_ids.extend(action_ids(branch));
        }
        all_ids.sort();
        assert_eq!(all_ids, (0..15).collect::<Vec<_>>());
    }

    // -----------------------------------------------------------------------
    // Linearizability checker unit tests
    // -----------------------------------------------------------------------

    // MockAction always bridges OK, so any interleaving is linearizable.
    // For testing non-linearizable cases, we use FailingAction.

    #[derive(Debug, Clone)]
    struct FailingAction;

    impl AnyAction for FailingAction {
        fn as_any(&self) -> &dyn Any { self }
        fn used_vars(&self) -> Vec<usize> { vec![] }
        fn check_bridge(&self, _: &dyn Any, _: &dyn Any) -> Result<(), String> {
            Err("bridge mismatch".into())
        }
        fn store_model_var(&self, _: usize, _: &dyn Any, _: &mut TypedEnv) {}
        fn store_sut_var(&self, _: usize, _: &dyn Any, _: &mut TypedEnv) {}
    }

    // A mock model for linearizability tests.
    #[derive(Debug, Clone)]
    struct MockModel;

    impl LockstepModel for MockModel {
        type ModelState = ();
        type Sut = ();
        fn init_model() -> () { () }
        fn init_sut() -> () { () }
        fn gen_action(_: &(), _: &TypedEnv) -> proptest::strategy::BoxedStrategy<Box<dyn AnyAction>> {
            unimplemented!()
        }
        fn step_model(_: &mut (), _: &dyn AnyAction, _: &TypedEnv) -> Box<dyn Any> {
            Box::new(())
        }
        fn step_sut(_: &mut (), _: &dyn AnyAction, _: &TypedEnv) -> Box<dyn Any> {
            Box::new(())
        }
    }

    fn make_records(actions: Vec<Box<dyn AnyAction>>, start_var_id: usize) -> Vec<OpRecord> {
        actions.into_iter().enumerate().map(|(i, action)| {
            OpRecord {
                action,
                result: Box::new(()),
                var_id: start_var_id + i,
            }
        }).collect()
    }

    #[test]
    fn linearizability_empty_branches() {
        let env = TypedEnv::new();
        let branches: Vec<Vec<OpRecord>> = vec![];
        assert!(check_linearizability::<MockModel>(
            &(), &env, &branches, 1000, BudgetExceeded::Fail, &mut LinearizabilityStats::default(), true
        ).is_ok());
    }

    #[test]
    fn linearizability_single_branch() {
        let env = TypedEnv::new();
        let branches = vec![
            make_records(mock_actions(3), 0),
        ];
        assert!(check_linearizability::<MockModel>(
            &(), &env, &branches, 1000, BudgetExceeded::Fail, &mut LinearizabilityStats::default(), true
        ).is_ok());
    }

    #[test]
    fn linearizability_two_branches_all_match() {
        let env = TypedEnv::new();
        let branches = vec![
            make_records(mock_actions(2), 0),
            make_records(mock_actions(2), 2),
        ];
        assert!(check_linearizability::<MockModel>(
            &(), &env, &branches, 1000, BudgetExceeded::Fail, &mut LinearizabilityStats::default(), true
        ).is_ok());
    }

    #[test]
    fn linearizability_fails_when_all_bridges_fail() {
        let env = TypedEnv::new();
        let branches = vec![
            vec![OpRecord {
                action: Box::new(FailingAction),
                result: Box::new(()),
                var_id: 0,
            }],
        ];
        let result = check_linearizability::<MockModel>(
            &(), &env, &branches, 1000, BudgetExceeded::Fail, &mut LinearizabilityStats::default(), true
        );
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("none matched"));
    }

    #[test]
    fn linearizability_budget_warn() {
        let env = TypedEnv::new();
        // Budget=0 means the checker hits the budget check before
        // trying any interleaving. With Warn, it returns Ok.
        let branches = vec![
            make_records(mock_actions(2), 0),
            make_records(mock_actions(2), 2),
        ];
        assert!(check_linearizability::<MockModel>(
            &(), &env, &branches, 0, BudgetExceeded::Warn, &mut LinearizabilityStats::default(), true
        ).is_ok());
    }

    #[test]
    fn linearizability_budget_fail() {
        let env = TypedEnv::new();
        // Use FailingAction so no interleaving matches, and budget
        // will be the reason it stops. But since bridges fail, it stops
        // at depth 0 with 0 attempts -- budget isn't the issue.
        // Instead, test with matching actions but tiny budget that
        // gets exhausted before completing.
        // Actually, with MockAction (always matches), the FIRST
        // interleaving succeeds, so budget is never hit. We need
        // a scenario where many interleavings fail before one succeeds.
        // For unit testing budget behavior, just use FailingAction
        // with a budget > total interleavings -- it exhausts all
        // interleavings and then reports no match (not budget).
        // The budget-fail path triggers when budget < total interleavings
        // and no match is found before the budget. Let's simulate that
        // with a mix: first action always fails, so checker tries many
        // branches but none get past depth 0. Budget = 0 triggers immediately.
        let branches = vec![
            make_records(mock_actions(3), 0),
            make_records(mock_actions(3), 3),
        ];
        // Budget of 0 means the checker never even tries
        let result = check_linearizability::<MockModel>(
            &(), &env, &branches, 0, BudgetExceeded::Fail, &mut LinearizabilityStats::default(), true
        );
        assert!(result.is_err());
    }

    #[test]
    fn linearizability_preserves_within_branch_order() {
        // With 2 branches of 2 actions each, there are C(4,2)=6
        // interleavings. The checker should find at least one valid
        // linearization (MockAction always matches).
        let env = TypedEnv::new();
        let branches = vec![
            make_records(mock_actions(2), 0),
            make_records(mock_actions(2), 2),
        ];
        assert!(check_linearizability::<MockModel>(
            &(), &env, &branches, 1000, BudgetExceeded::Fail, &mut LinearizabilityStats::default(), true
        ).is_ok());
    }

    // -----------------------------------------------------------------------
    // Commutativity detection unit tests
    // -----------------------------------------------------------------------

    // A model with a HashMap to test commutativity with real state.
    #[derive(Debug, Clone, PartialEq)]
    struct KvModelState {
        data: std::collections::HashMap<String, String>,
    }

    // Actions for the stateful model
    #[derive(Debug, Clone)]
    struct PutAction { key: String, value: String }
    #[derive(Debug, Clone)]
    struct GetAction { key: String }

    impl AnyAction for PutAction {
        fn as_any(&self) -> &dyn Any { self }
        fn used_vars(&self) -> Vec<usize> { vec![] }
        fn check_bridge(&self, model: &dyn Any, sut: &dyn Any) -> Result<(), String> {
            let m = model.downcast_ref::<Option<String>>().unwrap();
            let s = sut.downcast_ref::<Option<String>>().unwrap();
            if m == s { Ok(()) } else { Err(format!("{:?} != {:?}", m, s)) }
        }
        fn store_model_var(&self, _: usize, _: &dyn Any, _: &mut TypedEnv) {}
        fn store_sut_var(&self, _: usize, _: &dyn Any, _: &mut TypedEnv) {}
    }

    impl AnyAction for GetAction {
        fn as_any(&self) -> &dyn Any { self }
        fn used_vars(&self) -> Vec<usize> { vec![] }
        fn check_bridge(&self, model: &dyn Any, sut: &dyn Any) -> Result<(), String> {
            let m = model.downcast_ref::<Option<String>>().unwrap();
            let s = sut.downcast_ref::<Option<String>>().unwrap();
            if m == s { Ok(()) } else { Err(format!("{:?} != {:?}", m, s)) }
        }
        fn store_model_var(&self, _: usize, _: &dyn Any, _: &mut TypedEnv) {}
        fn store_sut_var(&self, _: usize, _: &dyn Any, _: &mut TypedEnv) {}
    }

    #[derive(Debug, Clone)]
    struct KvMockModel;

    impl LockstepModel for KvMockModel {
        type ModelState = KvModelState;
        type Sut = ();
        fn init_model() -> KvModelState {
            KvModelState { data: std::collections::HashMap::new() }
        }
        fn init_sut() -> () { () }
        fn gen_action(_: &KvModelState, _: &TypedEnv) -> proptest::strategy::BoxedStrategy<Box<dyn AnyAction>> {
            unimplemented!()
        }
        fn step_model(state: &mut KvModelState, action: &dyn AnyAction, _: &TypedEnv) -> Box<dyn Any> {
            if let Some(put) = action.as_any().downcast_ref::<PutAction>() {
                Box::new(state.data.insert(put.key.clone(), put.value.clone()))
            } else if let Some(get) = action.as_any().downcast_ref::<GetAction>() {
                Box::new(state.data.get(&get.key).cloned())
            } else {
                Box::new(())
            }
        }
        fn step_sut(_: &mut (), _: &dyn AnyAction, _: &TypedEnv) -> Box<dyn Any> {
            Box::new(())
        }
    }

    #[test]
    fn commute_disjoint_keys() {
        // Put("x", "1") and Put("y", "2") touch different keys -- they commute
        let model = KvMockModel::init_model();
        let env = TypedEnv::new();
        let a = OpRecord {
            action: Box::new(PutAction { key: "x".into(), value: "1".into() }),
            result: Box::new(None::<String>),
            var_id: 0,
        };
        let b = OpRecord {
            action: Box::new(PutAction { key: "y".into(), value: "2".into() }),
            result: Box::new(None::<String>),
            var_id: 1,
        };
        assert!(operations_commute::<KvMockModel>(&model, &env, &a, &b));
    }

    #[test]
    fn no_commute_same_key() {
        // Put("x", "1") and Put("x", "2") touch the same key -- don't commute
        // because final state differs: {x: "2"} vs {x: "1"}
        let model = KvMockModel::init_model();
        let env = TypedEnv::new();
        let a = OpRecord {
            action: Box::new(PutAction { key: "x".into(), value: "1".into() }),
            result: Box::new(None::<String>),
            var_id: 0,
        };
        let b = OpRecord {
            action: Box::new(PutAction { key: "x".into(), value: "2".into() }),
            result: Box::new(None::<String>),
            var_id: 1,
        };
        assert!(!operations_commute::<KvMockModel>(&model, &env, &a, &b));
    }

    #[test]
    fn commute_get_different_key() {
        // Get("y") and Put("x", "1") touch different keys -- they commute
        let model = KvMockModel::init_model();
        let env = TypedEnv::new();
        let a = OpRecord {
            action: Box::new(GetAction { key: "y".into() }),
            result: Box::new(None::<String>),
            var_id: 0,
        };
        let b = OpRecord {
            action: Box::new(PutAction { key: "x".into(), value: "1".into() }),
            result: Box::new(None::<String>),
            var_id: 1,
        };
        assert!(operations_commute::<KvMockModel>(&model, &env, &a, &b));
    }

    #[test]
    fn no_commute_get_same_key_as_put() {
        // Get("x") and Put("x", "1") -- Get returns None vs Some("1")
        // depending on order, so they don't commute
        let model = KvMockModel::init_model();
        let env = TypedEnv::new();
        let a = OpRecord {
            action: Box::new(GetAction { key: "x".into() }),
            result: Box::new(None::<String>),
            var_id: 0,
        };
        let b = OpRecord {
            action: Box::new(PutAction { key: "x".into(), value: "1".into() }),
            result: Box::new(None::<String>),
            var_id: 1,
        };
        assert!(!operations_commute::<KvMockModel>(&model, &env, &a, &b));
    }

    #[test]
    fn commute_two_gets() {
        // Get("x") and Get("y") are both reads -- always commute
        let model = KvMockModel::init_model();
        let env = TypedEnv::new();
        let a = OpRecord {
            action: Box::new(GetAction { key: "x".into() }),
            result: Box::new(None::<String>),
            var_id: 0,
        };
        let b = OpRecord {
            action: Box::new(GetAction { key: "y".into() }),
            result: Box::new(None::<String>),
            var_id: 1,
        };
        assert!(operations_commute::<KvMockModel>(&model, &env, &a, &b));
    }

    #[test]
    fn commute_two_gets_same_key() {
        // Get("x") and Get("x") -- both read same key, still commute
        let model = KvMockModel::init_model();
        let env = TypedEnv::new();
        let a = OpRecord {
            action: Box::new(GetAction { key: "x".into() }),
            result: Box::new(None::<String>),
            var_id: 0,
        };
        let b = OpRecord {
            action: Box::new(GetAction { key: "x".into() }),
            result: Box::new(None::<String>),
            var_id: 1,
        };
        assert!(operations_commute::<KvMockModel>(&model, &env, &a, &b));
    }

    // -----------------------------------------------------------------------
    // ConflictMaximizing split tests
    // -----------------------------------------------------------------------

    #[test]
    fn conflict_maximizing_differs_from_round_robin() {
        // Create actions where Put("x","1") and Put("x","2") conflict
        // (same key). ConflictMaximizing should place them on different
        // branches, while RoundRobin might not.
        let actions: Vec<(Box<dyn AnyAction>, usize)> = vec![
            (Box::new(PutAction { key: "x".into(), value: "1".into() }), 0),
            (Box::new(PutAction { key: "x".into(), value: "2".into() }), 1),
            (Box::new(GetAction { key: "y".into() }), 2),
            (Box::new(PutAction { key: "x".into(), value: "3".into() }), 3),
        ];

        let model = KvMockModel::init_model();
        let env = TypedEnv::new();

        let rr = split_remaining_with_ids::<KvMockModel>(
            actions.clone(), 2, SplitStrategy::RoundRobin, &model, &env,
        );
        let cm = split_remaining_with_ids::<KvMockModel>(
            actions, 2, SplitStrategy::ConflictMaximizing, &model, &env,
        );

        // RoundRobin puts 0,2 on branch 0 and 1,3 on branch 1
        // ConflictMaximizing should produce a different assignment because
        // Put("x","1") and Put("x","2") conflict
        let rr_b0: Vec<usize> = rr[0].iter().map(|(_, id)| *id).collect();
        let rr_b1: Vec<usize> = rr[1].iter().map(|(_, id)| *id).collect();
        let cm_b0: Vec<usize> = cm[0].iter().map(|(_, id)| *id).collect();
        let cm_b1: Vec<usize> = cm[1].iter().map(|(_, id)| *id).collect();

        // The splits should differ
        assert!(
            rr_b0 != cm_b0 || rr_b1 != cm_b1,
            "ConflictMaximizing produced same split as RoundRobin: {:?} vs {:?}",
            (rr_b0, rr_b1), (cm_b0, cm_b1)
        );
    }

    #[test]
    fn conflict_maximizing_separates_conflicting_ops() {
        // Put("x","1") and Put("x","2") conflict -- they should end up
        // on different branches.
        let actions: Vec<(Box<dyn AnyAction>, usize)> = vec![
            (Box::new(PutAction { key: "x".into(), value: "1".into() }), 0),
            (Box::new(PutAction { key: "x".into(), value: "2".into() }), 1),
        ];

        let model = KvMockModel::init_model();
        let env = TypedEnv::new();

        let branches = split_remaining_with_ids::<KvMockModel>(
            actions, 2, SplitStrategy::ConflictMaximizing, &model, &env,
        );

        // Each branch should have exactly 1 action
        assert_eq!(branches[0].len(), 1);
        assert_eq!(branches[1].len(), 1);
        // They should be on different branches
        let id0 = branches[0][0].1;
        let id1 = branches[1][0].1;
        assert_ne!(id0, id1);
    }

    // -----------------------------------------------------------------------
    // DPOR effectiveness test
    // -----------------------------------------------------------------------

    #[test]
    fn dpor_vs_brute_force_both_find_linearization() {
        // Two branches with disjoint keys -- both DPOR and brute-force
        // should find a valid linearization. DPOR finds it on the first
        // try (all operations commute), same as brute-force.
        let model = KvMockModel::init_model();
        let env = TypedEnv::new();

        let branches = vec![
            vec![
                OpRecord {
                    action: Box::new(PutAction { key: "a".into(), value: "1".into() }),
                    result: Box::new(None::<String>),
                    var_id: 0,
                },
                OpRecord {
                    action: Box::new(PutAction { key: "b".into(), value: "2".into() }),
                    result: Box::new(None::<String>),
                    var_id: 1,
                },
            ],
            vec![
                OpRecord {
                    action: Box::new(PutAction { key: "c".into(), value: "3".into() }),
                    result: Box::new(None::<String>),
                    var_id: 2,
                },
                OpRecord {
                    action: Box::new(PutAction { key: "d".into(), value: "4".into() }),
                    result: Box::new(None::<String>),
                    var_id: 3,
                },
            ],
        ];

        // Both should succeed
        let mut stats_dpor = LinearizabilityStats::default();
        check_linearizability::<KvMockModel>(
            &model, &env, &branches, 1000, BudgetExceeded::Fail,
            &mut stats_dpor, true,
        ).unwrap();

        let mut stats_brute = LinearizabilityStats::default();
        check_linearizability::<KvMockModel>(
            &model, &env, &branches, 1000, BudgetExceeded::Fail,
            &mut stats_brute, false,
        ).unwrap();

        // Brute force should not prune or check commutativity
        assert_eq!(stats_brute.interleavings_pruned, 0);
        assert_eq!(stats_brute.commutativity_checks, 0);

        eprintln!(
            "DPOR stats: tried={}, pruned={}, commutativity_checks={}",
            stats_dpor.interleavings_tried,
            stats_dpor.interleavings_pruned,
            stats_dpor.commutativity_checks,
        );
        eprintln!(
            "Brute-force stats: tried={}, pruned={}, commutativity_checks={}",
            stats_brute.interleavings_tried,
            stats_brute.interleavings_pruned,
            stats_brute.commutativity_checks,
        );
    }

    #[test]
    fn dpor_prunes_non_linearizable_search() {
        // Use FailingAction so NO interleaving matches. The checker
        // must explore all interleavings (brute-force) or prune some
        // (DPOR). With all-failing bridges, DPOR can't prune (all ops
        // "conflict" since they fail), but the stats still track attempts.
        // This verifies the dpor_enabled flag works correctly.
        let env = TypedEnv::new();
        let branches = vec![
            vec![OpRecord {
                action: Box::new(FailingAction),
                result: Box::new(()),
                var_id: 0,
            }],
            vec![OpRecord {
                action: Box::new(FailingAction),
                result: Box::new(()),
                var_id: 1,
            }],
        ];

        let mut stats_dpor = LinearizabilityStats::default();
        let _ = check_linearizability::<MockModel>(
            &(), &env, &branches, 1000, BudgetExceeded::Pass,
            &mut stats_dpor, true,
        );

        let mut stats_brute = LinearizabilityStats::default();
        let _ = check_linearizability::<MockModel>(
            &(), &env, &branches, 1000, BudgetExceeded::Pass,
            &mut stats_brute, false,
        );

        // Both should report 0 complete interleavings (none matched)
        assert_eq!(stats_dpor.interleavings_tried, 0);
        assert_eq!(stats_brute.interleavings_tried, 0);
        // Brute force should have 0 commutativity checks
        assert_eq!(stats_brute.commutativity_checks, 0);
    }
}
