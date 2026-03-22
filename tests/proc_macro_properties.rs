//! Property tests for the proc macro.
//!
//! Verifies that the proc macro generates correct code for various
//! type structures — transparent, opaque, composed, and auto-derived.

use proptest_lockstep::prelude::*;
use std::any::Any;

// ============================================================================
// Test: transparent types (real == model)
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
struct TransparentModel;

#[proptest_lockstep::lockstep_actions(state = TransparentModel)]
pub mod transparent_actions {
    #[action(real_return = "i32")]
    pub struct ReturnInt;

    #[action(real_return = "String")]
    pub struct ReturnString;

    #[action(real_return = "bool")]
    pub struct ReturnBool;

    #[action(real_return = "()")]
    pub struct ReturnUnit;

    #[action(real_return = "Option<i32>")]
    pub struct ReturnOption;

    #[action(real_return = "Result<String, bool>")]
    pub struct ReturnResult;

    #[action(real_return = "Vec<i32>")]
    pub struct ReturnVec;

    #[action(real_return = "(i32, String)")]
    pub struct ReturnTuple;

    #[action(real_return = "Option<(i32, String)>")]
    pub struct ReturnNestedOption;

    #[action(real_return = "Result<Vec<i32>, String>")]
    pub struct ReturnNestedResult;
}

#[test]
fn transparent_types_compile() {
    // If this compiles, the proc macro correctly generated bridges
    // for all transparent type structures
    let _ = transparent_actions::return_int(transparent_actions::ReturnInt);
    let _ = transparent_actions::return_string(transparent_actions::ReturnString);
    let _ = transparent_actions::return_bool(transparent_actions::ReturnBool);
    let _ = transparent_actions::return_unit(transparent_actions::ReturnUnit);
    let _ = transparent_actions::return_option(transparent_actions::ReturnOption);
    let _ = transparent_actions::return_result(transparent_actions::ReturnResult);
    let _ = transparent_actions::return_vec(transparent_actions::ReturnVec);
    let _ = transparent_actions::return_tuple(transparent_actions::ReturnTuple);
    let _ = transparent_actions::return_nested_option(transparent_actions::ReturnNestedOption);
    let _ = transparent_actions::return_nested_result(transparent_actions::ReturnNestedResult);
}

// ============================================================================
// Test: opaque types (real != model, with opaque_types mapping)
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
struct OpaqueModel;

#[derive(Debug, Clone, PartialEq)]
struct RealId(u64);

#[derive(Debug, Clone, PartialEq)]
struct ModelId(u64);

#[proptest_lockstep::lockstep_actions(state = OpaqueModel)]
pub mod opaque_actions {
    #[action(
        real_return = "RealId",
        model_return = "ModelId",
        opaque_types = { RealId => ModelId },
    )]
    pub struct Create;

    #[action(
        real_return = "Option<RealId>",
        model_return = "Option<ModelId>",
        opaque_types = { RealId => ModelId },
    )]
    pub struct MaybeCreate;

    #[action(
        real_return = "Result<RealId, String>",
        model_return = "Result<ModelId, String>",
        opaque_types = { RealId => ModelId },
    )]
    pub struct TryCreate;

    #[action(
        real_return = "Result<(RealId, String), bool>",
        model_return = "Result<(ModelId, String), bool>",
        opaque_types = { RealId => ModelId },
    )]
    pub struct CreateWithPath;
}

#[test]
fn opaque_types_compile() {
    let _ = opaque_actions::create(opaque_actions::Create);
    let _ = opaque_actions::maybe_create(opaque_actions::MaybeCreate);
    let _ = opaque_actions::try_create(opaque_actions::TryCreate);
    let _ = opaque_actions::create_with_path(opaque_actions::CreateWithPath);
}

// ============================================================================
// Test: explicit bridge (backwards compatibility)
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
struct ExplicitModel;

#[proptest_lockstep::lockstep_actions(state = ExplicitModel)]
pub mod explicit_actions {
    #[action(
        real_return = "i32",
        bridge = "Transparent<i32>",
    )]
    pub struct WithBridge;

    #[action(
        real_return = "Result<String, bool>",
        bridge = "ResultBridge<Transparent<String>, Transparent<bool>>",
    )]
    pub struct WithComposedBridge;
}

#[test]
fn explicit_bridges_compile() {
    let _ = explicit_actions::with_bridge(explicit_actions::WithBridge);
    let _ = explicit_actions::with_composed_bridge(explicit_actions::WithComposedBridge);
}

// ============================================================================
// Test: uses attribute for variable tracking
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
struct UsesModel;

type CreateResult = Result<(RealId, String), bool>;

#[proptest_lockstep::lockstep_actions(state = UsesModel)]
pub mod uses_actions {
    #[action(real_return = "i32")]
    pub struct Independent;

    #[action(
        real_return = "bool",
        uses = [handle],
    )]
    pub struct Dependent {
        pub handle: GVar<CreateResult, RealId, OpComp<OpOk, OpFst, (RealId, String)>>,
    }
}

#[test]
fn uses_attribute_compiles() {
    let _ = uses_actions::independent(uses_actions::Independent);
    // Dependent requires a GVar — just check the type exists
    assert_eq!(std::mem::size_of::<uses_actions::Dependent>(), std::mem::size_of::<GVar<CreateResult, RealId, OpComp<OpOk, OpFst, (RealId, String)>>>());
}
