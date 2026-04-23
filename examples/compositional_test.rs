#![allow(dead_code)]
//! Compositional lockstep testing demonstration.
//!
//! Shows modular testing: a counter subsystem and a log subsystem
//! are tested independently, then their composition is verified.
//! The compositional bisimulation theorem guarantees that if both
//! subsystems pass, their product is correct.
//!
//! Run with: `cargo test --example compositional_test`

use std::any::Any;

use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;
use proptest_lockstep::compositional::{
    run_composed_test, verify_composition, IncrementalComposition, BridgePrecision,
};

// ============================================================================
// Subsystem A: Counter
// ============================================================================

#[derive(Debug)]
struct Counter { value: i32 }

#[derive(Debug, Clone, PartialEq)]
struct CounterModel { value: i32 }

#[proptest_lockstep::lockstep_actions(state = CounterModel)]
pub mod ctr {
    #[action(real_return = "i32")]
    pub struct Inc;

    #[action(real_return = "i32")]
    pub struct Dec;

    #[action(real_return = "i32")]
    pub struct Get;
}

#[derive(Debug, Clone)]
struct CounterLockstep;

impl ctr::CtrModelInterp for CounterLockstep {
    type State = CounterModel;
    fn inc(s: &mut CounterModel, _: &ctr::Inc, _: &TypedEnv) -> i32 { s.value += 1; s.value }
    fn dec(s: &mut CounterModel, _: &ctr::Dec, _: &TypedEnv) -> i32 { s.value -= 1; s.value }
    fn get(s: &mut CounterModel, _: &ctr::Get, _: &TypedEnv) -> i32 { s.value }
}

impl ctr::CtrSutInterp for CounterLockstep {
    type Sut = Counter;
    fn inc(s: &mut Counter, _: &ctr::Inc, _: &TypedEnv) -> i32 { s.value += 1; s.value }
    fn dec(s: &mut Counter, _: &ctr::Dec, _: &TypedEnv) -> i32 { s.value -= 1; s.value }
    fn get(s: &mut Counter, _: &ctr::Get, _: &TypedEnv) -> i32 { s.value }
}

impl LockstepModel for CounterLockstep {
    type ModelState = CounterModel;
    type Sut = Counter;
    fn init_model() -> CounterModel { CounterModel { value: 0 } }
    fn init_sut() -> Counter { Counter { value: 0 } }
    fn gen_action(_: &CounterModel, _: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        prop_oneof![
            Just(ctr::inc(ctr::Inc)),
            Just(ctr::dec(ctr::Dec)),
            Just(ctr::get(ctr::Get)),
        ].boxed()
    }
    fn step_model(s: &mut CounterModel, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        ctr::dispatch_model::<CounterLockstep>(s, a, e)
    }
    fn step_sut(s: &mut Counter, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        ctr::dispatch_sut::<CounterLockstep>(s, a, e)
    }
}

// ============================================================================
// Subsystem B: Logger
// ============================================================================

#[derive(Debug)]
struct Logger { entries: Vec<String> }

#[derive(Debug, Clone, PartialEq)]
struct LogModel { entries: Vec<String> }

#[proptest_lockstep::lockstep_actions(state = LogModel)]
pub mod log_actions {
    #[action(real_return = "usize")]
    pub struct Append { pub msg: String }

    #[action(real_return = "Option<String>")]
    pub struct Read { pub index: usize }

    #[action(real_return = "usize")]
    pub struct Len;
}

#[derive(Debug, Clone)]
struct LogLockstep;

impl log_actions::LogActionsModelInterp for LogLockstep {
    type State = LogModel;
    fn append(s: &mut LogModel, a: &log_actions::Append, _: &TypedEnv) -> usize {
        s.entries.push(a.msg.clone()); s.entries.len() - 1
    }
    fn read(s: &mut LogModel, a: &log_actions::Read, _: &TypedEnv) -> Option<String> {
        s.entries.get(a.index).cloned()
    }
    fn len(s: &mut LogModel, _: &log_actions::Len, _: &TypedEnv) -> usize {
        s.entries.len()
    }
}

impl log_actions::LogActionsSutInterp for LogLockstep {
    type Sut = Logger;
    fn append(s: &mut Logger, a: &log_actions::Append, _: &TypedEnv) -> usize {
        s.entries.push(a.msg.clone()); s.entries.len() - 1
    }
    fn read(s: &mut Logger, a: &log_actions::Read, _: &TypedEnv) -> Option<String> {
        s.entries.get(a.index).cloned()
    }
    fn len(s: &mut Logger, _: &log_actions::Len, _: &TypedEnv) -> usize {
        s.entries.len()
    }
}

impl LockstepModel for LogLockstep {
    type ModelState = LogModel;
    type Sut = Logger;
    fn init_model() -> LogModel { LogModel { entries: Vec::new() } }
    fn init_sut() -> Logger { Logger { entries: Vec::new() } }
    fn gen_action(_: &LogModel, _: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        prop_oneof![
            proptest::sample::select(vec!["hello", "world", "test"])
                .prop_map(|m| log_actions::append(log_actions::Append { msg: m.to_string() })),
            (0usize..5).prop_map(|i| log_actions::read(log_actions::Read { index: i })),
            Just(log_actions::len(log_actions::Len)),
        ].boxed()
    }
    fn step_model(s: &mut LogModel, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        log_actions::dispatch_model::<LogLockstep>(s, a, e)
    }
    fn step_sut(s: &mut Logger, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        log_actions::dispatch_sut::<LogLockstep>(s, a, e)
    }
}

fn main() {
    println!("Run with `cargo test --example compositional_test`");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test each subsystem independently.
    #[test]
    fn counter_passes_independently() {
        proptest_lockstep::runner::run_lockstep_test::<CounterLockstep>(1..20);
    }

    #[test]
    fn logger_passes_independently() {
        proptest_lockstep::runner::run_lockstep_test::<LogLockstep>(1..20);
    }

    /// Compositional test: verify both subsystems together.
    /// The compositional_bisim theorem guarantees that if both pass
    /// independently, their product is correct.
    #[test]
    fn composition_is_sound() {
        let counter_trace: Vec<Box<dyn AnyAction>> = vec![
            ctr::inc(ctr::Inc),
            ctr::inc(ctr::Inc),
            ctr::get(ctr::Get),
            ctr::dec(ctr::Dec),
        ];

        let log_trace: Vec<Box<dyn AnyAction>> = vec![
            log_actions::append(log_actions::Append { msg: "start".into() }),
            log_actions::append(log_actions::Append { msg: "middle".into() }),
            log_actions::len(log_actions::Len),
            log_actions::read(log_actions::Read { index: 0 }),
        ];

        run_composed_test::<CounterLockstep, LogLockstep>(
            &counter_trace,
            &log_trace,
        );
    }

    /// Verify composition and get statistics.
    #[test]
    fn verify_composition_stats() {
        let counter_trace: Vec<Box<dyn AnyAction>> = vec![
            ctr::inc(ctr::Inc),
            ctr::get(ctr::Get),
        ];

        let log_trace: Vec<Box<dyn AnyAction>> = vec![
            log_actions::append(log_actions::Append { msg: "hello".into() }),
            log_actions::len(log_actions::Len),
        ];

        let result = verify_composition::<CounterLockstep, LogLockstep>(
            &counter_trace,
            &log_trace,
        );

        assert!(result.composition_sound);
        assert!(result.left_passes);
        assert!(result.right_passes);
    }

    /// Incremental compositional testing: test subsystems independently,
    /// then re-test only the changed one after bridge refinement.
    ///
    /// The key guarantee (from `product_refines_bisim` in Lean):
    /// refining one component's bridges doesn't invalidate the other
    /// component's test results.
    #[test]
    fn incremental_composition() {
        let mut comp = IncrementalComposition::new();

        // Phase 1: test both subsystems
        assert!(!comp.is_sound()); // nothing tested yet

        comp.test_left::<CounterLockstep>(1..10);
        assert!(!comp.is_sound()); // only left tested

        comp.test_right::<LogLockstep>(1..10);
        assert!(comp.is_sound()); // both pass → composition sound

        let result = comp.result();
        assert_eq!(result.left_tests_run, 1);
        assert_eq!(result.right_tests_run, 1);

        // Phase 2: upgrade Logger's bridges from Opaque to Transparent
        // This automatically invalidates Logger's previous result
        // (finer precision requires re-testing)
        comp.set_right_precision(BridgePrecision::Transparent);
        assert!(!comp.is_sound()); // logger invalidated by precision upgrade

        // Re-test Logger at the new precision
        // Counter's result is REUSED -- not re-tested
        comp.retest_right::<LogLockstep>(1..15);
        assert!(comp.is_sound()); // sound again at finer precision

        let result = comp.result();
        assert_eq!(result.left_tests_run, 1);   // counter NOT re-tested
        assert_eq!(result.right_tests_run, 2);   // logger re-tested
        assert_eq!(result.right_precision, BridgePrecision::Transparent);

        // Phase 3: downgrade Logger back to Mixed -- previous Transparent
        // result covers Mixed (finer → coarser is free by refines_strengthen_bisim)
        comp.set_right_precision(BridgePrecision::Mixed);
        assert!(comp.is_sound()); // still sound -- no re-test needed!
        assert_eq!(comp.result().right_tests_run, 2); // still 2, not 3

        // Phase 4: invalidate counter (simulate implementation change)
        comp.invalidate_left();
        assert!(!comp.is_sound()); // composition broken

        // Re-test counter
        comp.retest_left::<CounterLockstep>(1..10);
        assert!(comp.is_sound()); // sound again
    }
}
