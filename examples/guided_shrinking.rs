#![allow(dead_code)]
//! Bisimulation-guided shrinking demonstration.
//!
//! Shows how the framework minimizes counterexamples using the
//! bisimulation structure. A buggy stack with an off-by-one error
//! is tested, and the shrinking algorithm removes irrelevant
//! setup actions to produce a minimal failing trace.
//!
//! Run with: `cargo test --example guided_shrinking`

use std::any::Any;

use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;
use proptest_lockstep::shrinking::{find_failure_depth, minimize_trace, minimize_and_report};

// ============================================================================
// Buggy stack (same as bug_detection example)
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
    fn len(&self) -> usize { self.items.len() }
}

#[derive(Debug, Clone, PartialEq)]
struct StackModel { items: Vec<i32> }

#[proptest_lockstep::lockstep_actions(state = StackModel)]
mod stack_actions {
    #[action(real_return = "()")]
    pub struct Push { pub value: i32 }

    #[action(real_return = "Option<i32>")]
    pub struct Pop;

    #[action(real_return = "usize")]
    pub struct Len;
}

#[derive(Debug, Clone)]
struct BuggyStackLockstep;

impl stack_actions::StackActionsModelInterp for BuggyStackLockstep {
    type State = StackModel;
    fn push(s: &mut StackModel, a: &stack_actions::Push, _: &TypedEnv) {
        s.items.push(a.value);
    }
    fn pop(s: &mut StackModel, _: &stack_actions::Pop, _: &TypedEnv) -> Option<i32> {
        s.items.pop()
    }
    fn len(s: &mut StackModel, _: &stack_actions::Len, _: &TypedEnv) -> usize {
        s.items.len()
    }
}

impl stack_actions::StackActionsSutInterp for BuggyStackLockstep {
    type Sut = BuggyStack;
    fn push(s: &mut BuggyStack, a: &stack_actions::Push, _: &TypedEnv) {
        s.push(a.value);
    }
    fn pop(s: &mut BuggyStack, _: &stack_actions::Pop, _: &TypedEnv) -> Option<i32> {
        s.pop()
    }
    fn len(s: &mut BuggyStack, _: &stack_actions::Len, _: &TypedEnv) -> usize {
        s.len()
    }
}

impl LockstepModel for BuggyStackLockstep {
    type ModelState = StackModel;
    type Sut = BuggyStack;
    fn init_model() -> StackModel { StackModel { items: Vec::new() } }
    fn init_sut() -> BuggyStack { BuggyStack::new() }
    fn gen_action(_: &StackModel, _: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        prop_oneof![
            3 => (0i32..10).prop_map(|v| stack_actions::push(stack_actions::Push { value: v })),
            2 => Just(stack_actions::pop(stack_actions::Pop)),
            1 => Just(stack_actions::len(stack_actions::Len)),
        ].boxed()
    }
    fn step_model(s: &mut StackModel, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        stack_actions::dispatch_model::<BuggyStackLockstep>(s, a, e)
    }
    fn step_sut(s: &mut BuggyStack, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        stack_actions::dispatch_sut::<BuggyStackLockstep>(s, a, e)
    }
}

fn main() {
    println!("Run with `cargo test --example guided_shrinking`");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Demonstrates that find_failure_depth correctly identifies
    /// the step where the bug manifests.
    #[test]
    fn finds_failure_depth() {
        // Construct a trace that triggers the bug:
        // Push(1), Push(2), Pop — bug manifests at Pop (step 2)
        let trace: Vec<Box<dyn AnyAction>> = vec![
            stack_actions::push(stack_actions::Push { value: 1 }),
            stack_actions::push(stack_actions::Push { value: 2 }),
            stack_actions::pop(stack_actions::Pop),
        ];

        let failure = find_failure_depth::<BuggyStackLockstep>(&trace);
        assert!(failure.is_some(), "Should find a failure");
        let info = failure.unwrap();
        assert_eq!(info.failure_depth, 2, "Bug is at step 2 (the Pop)");
    }

    /// Demonstrates that minimize_trace removes irrelevant actions.
    /// Starting with a longer trace, the minimizer should reduce it
    /// to the minimal trigger: Push, Push, Pop.
    #[test]
    fn minimizes_trace() {
        // A longer trace with unnecessary actions (Len checks, extra pushes)
        let trace: Vec<Box<dyn AnyAction>> = vec![
            stack_actions::len(stack_actions::Len),             // irrelevant
            stack_actions::push(stack_actions::Push { value: 5 }), // necessary
            stack_actions::len(stack_actions::Len),             // irrelevant
            stack_actions::push(stack_actions::Push { value: 3 }), // necessary
            stack_actions::len(stack_actions::Len),             // irrelevant
            stack_actions::pop(stack_actions::Pop),             // triggers bug
        ];

        let result = minimize_trace::<BuggyStackLockstep>(&trace);
        assert!(result.is_some(), "Should produce a minimized trace");
        let shrunk = result.unwrap();

        // The minimal trace should be: Push, Push, Pop (3 actions)
        assert_eq!(
            shrunk.minimal_trace.len(), 3,
            "Minimal trace should be 3 actions (Push, Push, Pop), got {}",
            shrunk.minimal_trace.len(),
        );
        assert!(
            shrunk.actions_removed >= 3,
            "Should have removed at least 3 irrelevant Len checks, removed {}",
            shrunk.actions_removed,
        );
    }

    /// Full demonstration: minimize_and_report produces a detailed
    /// minimal counterexample with diagnostic output.
    #[test]
    fn full_minimize_and_report() {
        let trace: Vec<Box<dyn AnyAction>> = vec![
            stack_actions::push(stack_actions::Push { value: 7 }),
            stack_actions::len(stack_actions::Len),
            stack_actions::push(stack_actions::Push { value: 3 }),
            stack_actions::push(stack_actions::Push { value: 9 }),
            stack_actions::len(stack_actions::Len),
            stack_actions::pop(stack_actions::Pop),  // bug at this Pop
            stack_actions::push(stack_actions::Push { value: 1 }),  // after failure — irrelevant
        ];

        let result = minimize_and_report::<BuggyStackLockstep>(&trace);

        // Should have removed actions after the failure and irrelevant
        // Len checks before it
        assert!(
            result.minimal_trace.len() <= 4,
            "Should minimize to at most 4 actions, got {}",
            result.minimal_trace.len(),
        );
        assert!(result.actions_removed > 0);
    }
}
