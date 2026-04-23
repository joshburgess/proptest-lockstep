#![allow(dead_code)]
//! Differential bridge testing demonstration.
//!
//! Shows how the framework detects overly-coarse bridges that hide
//! real discrepancies. Uses a file system where the `Open` action's
//! bridge uses `Opaque` for handles -- but the handles actually
//! differ in a detectable way.
//!
//! Two tests demonstrate the differential technique:
//! 1. A system where handles INTENTIONALLY differ (opaque is correct)
//!    -- no bridge weakness detected
//! 2. A system where handles ACCIDENTALLY differ (opaque hides a bug)
//!    -- bridge weakness detected
//!
//! Run with: `cargo test --example differential_bridge`

use std::any::Any;
use std::collections::HashMap;

use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;
use proptest_lockstep::differential::{DifferentialBridgeModel, DifferentialConfig};

// ============================================================================
// A system with intentionally different handle types
// ============================================================================

/// Real handle: wraps an ID.
#[derive(Debug, Clone, PartialEq)]
struct RealHandle(u64);

/// Model handle: wraps an ID -- may differ from real handle.
#[derive(Debug, Clone, PartialEq)]
struct ModelHandle(u64);

/// A simple registry that maps handles to values.
#[derive(Debug)]
struct Registry {
    data: HashMap<u64, String>,
    next_id: u64,
}

impl Registry {
    fn new() -> Self {
        Registry { data: HashMap::new(), next_id: 0 }
    }

    fn create(&mut self, value: &str) -> RealHandle {
        let id = self.next_id;
        self.next_id += 1;
        self.data.insert(id, value.to_string());
        RealHandle(id)
    }

    fn lookup(&self, handle: u64) -> Option<String> {
        self.data.get(&handle).cloned()
    }
}

/// Model registry -- assigns IDs differently (offset by 1000).
/// This simulates the common case where model and SUT use different
/// ID schemes but are semantically equivalent.
#[derive(Debug, Clone, PartialEq)]
struct ModelRegistry {
    data: HashMap<u64, String>,
    next_id: u64,
}

impl ModelRegistry {
    fn new() -> Self {
        // IDs start at 100 (different from SUT's 0) to demonstrate
        // that Opaque hides this difference
        ModelRegistry { data: HashMap::new(), next_id: 100 }
    }

    fn create(&mut self, value: &str) -> ModelHandle {
        let id = self.next_id;
        self.next_id += 1;
        self.data.insert(id, value.to_string());
        ModelHandle(id)
    }

    fn lookup(&self, handle: u64) -> Option<String> {
        self.data.get(&handle).cloned()
    }
}

// ============================================================================
// Actions
// ============================================================================

#[proptest_lockstep::lockstep_actions(state = ModelRegistry)]
pub mod reg {
    // Create returns a handle. The bridge uses Opaque because
    // RealHandle and ModelHandle are different types with different IDs.
    #[action(
        real_return = "RealHandle",
        model_return = "ModelHandle",
        opaque_types = { RealHandle => ModelHandle },
    )]
    pub struct Create {
        pub value: String,
    }

    // Lookup returns the value -- uses Transparent (should match exactly).
    #[action(real_return = "Option<String>")]
    pub struct Lookup {
        pub id: u64,
    }
}

// ============================================================================
// Interpreters
// ============================================================================

#[derive(Debug, Clone)]
struct RegistryLockstep;

impl reg::RegModelInterp for RegistryLockstep {
    type State = ModelRegistry;
    fn create(s: &mut ModelRegistry, a: &reg::Create, _: &TypedEnv) -> ModelHandle {
        s.create(&a.value)
    }
    fn lookup(s: &mut ModelRegistry, a: &reg::Lookup, _: &TypedEnv) -> Option<String> {
        s.lookup(a.id)
    }
}

impl reg::RegSutInterp for RegistryLockstep {
    type Sut = Registry;
    fn create(s: &mut Registry, a: &reg::Create, _: &TypedEnv) -> RealHandle {
        s.create(&a.value)
    }
    fn lookup(s: &mut Registry, a: &reg::Lookup, _: &TypedEnv) -> Option<String> {
        s.lookup(a.id)
    }
}

impl LockstepModel for RegistryLockstep {
    type ModelState = ModelRegistry;
    type Sut = Registry;
    fn init_model() -> ModelRegistry { ModelRegistry::new() }
    fn init_sut() -> Registry { Registry::new() }
    fn gen_action(_: &ModelRegistry, _: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        let vals = vec!["alice", "bob", "charlie"];
        // Only Create actions -- Lookup by raw ID doesn't work when
        // model and SUT use different ID schemes. (In a full test,
        // you'd use GVar/opaque handle resolution for lookups.)
        proptest::sample::select(vals)
            .prop_map(|v| reg::create(reg::Create { value: v.to_string() }))
            .boxed()
    }
    fn step_model(s: &mut ModelRegistry, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        reg::dispatch_model::<RegistryLockstep>(s, a, e)
    }
    fn step_sut(s: &mut Registry, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        reg::dispatch_sut::<RegistryLockstep>(s, a, e)
    }
}

// ============================================================================
// DifferentialBridgeModel
// ============================================================================

impl DifferentialBridgeModel for RegistryLockstep {
    fn fine_check(
        action: &dyn AnyAction,
        model_result: &dyn Any,
        sut_result: &dyn Any,
    ) -> Result<(), String> {
        let a = action.as_any().downcast_ref::<reg::AnyRegAction>().unwrap();
        match a {
            reg::AnyRegAction::Create(_) => {
                // Fine check: compare handle IDs directly (Transparent
                // instead of Opaque). This WILL fail because model uses
                // IDs starting at 1000 while SUT uses IDs starting at 0.
                let real = sut_result.downcast_ref::<RealHandle>().unwrap();
                let model = model_result.downcast_ref::<ModelHandle>().unwrap();
                if real.0 == model.0 {
                    Ok(())
                } else {
                    Err(format!(
                        "  Handle IDs differ: real={}, model={}",
                        real.0, model.0
                    ))
                }
            }
            reg::AnyRegAction::Lookup(_) => {
                // Lookup uses Transparent already -- fine check is the same
                action.check_bridge(model_result, sut_result)
            }
        }
    }
}

fn main() {
    println!("Run with `cargo test --example differential_bridge`");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Standard lockstep passes: the Opaque bridge on handles correctly
    /// allows different IDs (the handles are semantically equivalent
    /// even though their IDs differ).
    #[test]
    fn standard_lockstep_passes() {
        proptest_lockstep::runner::run_lockstep_test::<RegistryLockstep>(1..20);
    }

    /// Differential bridge testing: detects that the Opaque bridge on
    /// Create handles is hiding the fact that handle IDs differ.
    ///
    /// This is EXPECTED -- the IDs intentionally differ (model starts
    /// at 1000, SUT starts at 0). The bridge weakness tells the user:
    /// "your Opaque bridge is hiding a difference -- is this intentional?"
    #[test]
    #[should_panic(expected = "Bridge weakness detected")]
    fn differential_catches_hidden_difference() {
        proptest_lockstep::differential::run_differential_test::<RegistryLockstep>(
            DifferentialConfig {
                cases: 50,
                min_ops: 2,
                max_ops: 10,
                fail_on_weakness: true,
            },
        );
    }

    /// Non-failing mode: collect weaknesses without panicking.
    #[test]
    fn differential_collects_weaknesses() {
        let stats = proptest_lockstep::differential::run_differential_test::<RegistryLockstep>(
            DifferentialConfig {
                cases: 50,
                min_ops: 2,
                max_ops: 10,
                fail_on_weakness: false,
            },
        );
        assert!(
            stats.weaknesses_found > 0,
            "Expected to find bridge weaknesses, got: {stats}"
        );
    }
}
