//! Concurrent lockstep testing via Shuttle.
//!
//! This module provides infrastructure for testing stateful APIs under
//! concurrent access. Neither `quickcheck-lockstep` nor Hedgehog offers
//! this — it's a capability unique to the Rust version.
//!
//! The approach:
//! 1. Generate a sequence of actions via the lockstep model.
//! 2. Split the sequence into a sequential prefix and N parallel branches.
//! 3. Execute the prefix sequentially against the SUT (with lockstep checks).
//! 4. Execute the branches concurrently under Shuttle's randomized scheduler.
//! 5. Verify the SUT doesn't panic under concurrent access.
//!
//! **Current limitations:** This module verifies crash-absence and
//! panic-freedom under concurrent access, NOT full linearizability.
//! Linearizability checking (verifying that concurrent results match
//! some sequential model execution) requires collecting results across
//! thread boundaries, which is planned for 0.2. The groundwork is in
//! place: `TypedEnv` values are already `Send`, so the remaining work
//! is a `ConcurrentLockstepModel` extension trait and an interleaving
//! checker.
//!
//! Requires the `concurrent` feature flag: `proptest-lockstep = { features = ["concurrent"] }`.

use std::fmt::Debug;

use crate::action::AnyAction;
use crate::env::TypedEnv;
use crate::model::LockstepModel;

/// Strategy for distributing actions across concurrent branches.
#[derive(Debug, Clone, Copy)]
pub enum SplitStrategy {
    /// Assign actions to branches in round-robin order (0, 1, 2, 0, 1, 2, ...).
    RoundRobin,
    /// Assign actions to branches using a deterministic seeded hash.
    /// The same seed always produces the same split, ensuring reproducibility.
    Random { seed: u64 },
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
}

impl Default for ConcurrentConfig {
    fn default() -> Self {
        ConcurrentConfig {
            iterations: 100,
            prefix_len: 5,
            branch_len: 5,
            branch_count: 2,
            split_strategy: SplitStrategy::RoundRobin,
        }
    }
}

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
                // Simple deterministic hash: mix seed with index
                let mut h = seed.wrapping_mul(6364136223846793005).wrapping_add(i as u64);
                h ^= h >> 33;
                h = h.wrapping_mul(0xff51afd7ed558ccd);
                h ^= h >> 33;
                (h as usize) % count
            }
        };
        branches[branch_idx].push(action);
    }

    (prefix, branches)
}

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

/// Run a concurrent lockstep test using Shuttle's randomized scheduler.
///
/// Generates action sequences, splits them into a prefix and N parallel
/// branches, executes them concurrently under Shuttle, and verifies that
/// the SUT doesn't panic under concurrent access.
///
/// **Note:** This tests crash-absence, not linearizability. The SUT is
/// verified to be panic-free and deadlock-free under randomized schedules.
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
    M::ModelState: Send + Sync,
    M::Sut: Send,
{
    lockstep_concurrent_with_check::<M, _>(config, |_| {});
}

/// Run a concurrent lockstep test with a final state check.
///
/// Same as [`lockstep_concurrent`], but after all concurrent branches
/// complete, calls `check_final` with a reference to the SUT. Use this
/// to verify that the SUT's final state is consistent after concurrent
/// operations — an intermediate guarantee between crash-absence and
/// full linearizability.
///
/// # Example
///
/// ```ignore
/// lockstep_concurrent_with_check::<MyModel, _>(config, |sut| {
///     // Verify the SUT is in a consistent state
///     assert!(sut.is_consistent());
/// });
/// ```
#[cfg(feature = "concurrent")]
pub fn lockstep_concurrent_with_check<M, F>(config: ConcurrentConfig, check_final: F)
where
    M: LockstepModel + Send + Sync,
    M::ModelState: Send + Sync,
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

            // Generate actions sequentially (each depends on model state)
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

            let (prefix, branches) = split_for_parallel(
                &actions,
                config.prefix_len,
                config.branch_count,
                config.split_strategy,
            );

            // Execute prefix sequentially (with lockstep verification)
            let (_model_state, sut, _model_env, sut_env) = run_prefix::<M>(&prefix);

            // Execute branches concurrently under Shuttle.
            let sut = shuttle::sync::Arc::new(shuttle::sync::Mutex::new(sut));
            let sut_env = shuttle::sync::Arc::new(shuttle::sync::Mutex::new(sut_env));

            let mut handles = Vec::new();

            for (branch_id, branch) in branches.into_iter().enumerate() {
                let sut_ref = sut.clone();
                let env_ref = sut_env.clone();
                let handle = shuttle::thread::spawn(move || {
                    let mut trace: Vec<String> = Vec::new();
                    for (step, action) in branch.iter().enumerate() {
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

            // Final state check
            let final_sut = sut.lock().unwrap();
            check_final(&final_sut);
        },
        config.iterations,
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::any::Any;

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
        // At least one branch should differ with high probability
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
}
