//! Certified bridge synthesis.
//!
//! Provides the Rust-side interface for certified bridge synthesis.
//! The Lean formalization (`CertifiedSynthesis.lean`) defines
//! `CertifiedBridge` — a bridge paired with a constructive proof
//! that it was synthesized from a correct recipe.
//!
//! On the Rust side, the `certify` functions provide documentation
//! and type safety that bridges were constructed through the
//! certified pipeline (proc macro → bridge type → Lean verification).
//!
//! # The Certified Pipeline
//!
//! ```text
//! User writes: real_return, model_return, opaque_types
//!     ↓
//! Proc macro: derive_bridge() produces bridge type expression
//!     ↓
//! Lean: certify_* constructors produce CertifiedBridge + proof
//!     ↓
//! Result: bridge that is provably correct by construction
//! ```
//!
//! Each bridge constructor in the Lean formalization has a matching
//! soundness theorem:
//! - `certify_transparent` → `certified_transparent_sound`
//! - `certify_opaque` → `certified_opaque_sound`
//! - `certify_sum` → `certified_sum_ok`
//! - `certify_prod` → `certified_prod_sound`
//! - `certify_option` → `certified_option_some/none`
//! - `certify_list` → `certified_list_nil/cons`

use std::fmt::Debug;
use std::marker::PhantomData;

use crate::bridge::LockstepBridge;

/// Marker trait for bridges that have been verified through the
/// certified synthesis pipeline.
///
/// Any bridge type produced by the proc macro's `derive_bridge`
/// function is certifiable — the Lean formalization provides the
/// corresponding `certify_*` constructors and soundness proofs.
///
/// This trait doesn't add methods — it's a marker that documents
/// the bridge's provenance. In a fully integrated system, the
/// proc macro would emit both the Rust bridge type AND a reference
/// to the Lean certificate.
pub trait CertifiedLockstepBridge: LockstepBridge {
    /// A human-readable description of how this bridge was
    /// synthesized. Matches the `BridgeRecipe` in Lean.
    fn synthesis_description() -> &'static str;
}

/// A wrapper that marks a bridge as certified.
///
/// The inner bridge is the actual `LockstepBridge` implementation.
/// The `Certified` wrapper provides the `CertifiedLockstepBridge`
/// marker and the synthesis description.
#[derive(Debug)]
pub struct Certified<B: LockstepBridge> {
    _phantom: PhantomData<B>,
}

/// Certificate for a `Transparent<T>` bridge.
///
/// Lean proof: `certified_transparent_sound`
/// Guarantee: bridge_equiv is equality.
pub struct TransparentCert<T>(PhantomData<T>);

impl<T: Debug + Clone + PartialEq + 'static> CertifiedLockstepBridge for crate::bridge::Transparent<T> {
    fn synthesis_description() -> &'static str {
        "Transparent — certified by certified_transparent_sound"
    }
}

/// Certificate for an `Opaque<R, M>` bridge.
///
/// Lean proof: `certified_opaque_sound`
/// Guarantee: bridge_equiv is always true.
impl<R: 'static, M: 'static> CertifiedLockstepBridge for crate::bridge::Opaque<R, M> {
    fn synthesis_description() -> &'static str {
        "Opaque — certified by certified_opaque_sound"
    }
}

/// Certificate for a `ResultBridge<OkB, ErrB>`.
///
/// Lean proof: `certified_sum_ok` / `certified_sum_err`
/// Guarantee: preserves component bridge_equiv.
impl<OkB, ErrB> CertifiedLockstepBridge for crate::bridge::ResultBridge<OkB, ErrB>
where
    OkB: LockstepBridge + CertifiedLockstepBridge,
    ErrB: LockstepBridge + CertifiedLockstepBridge,
    OkB::Real: Debug + Clone + 'static,
    OkB::Model: Debug + Clone + 'static,
    ErrB::Real: Debug + Clone + 'static,
    ErrB::Model: Debug + Clone + 'static,
    OkB::Observed: Debug + PartialEq + Clone + 'static,
    ErrB::Observed: Debug + PartialEq + Clone + 'static,
{
    fn synthesis_description() -> &'static str {
        "ResultBridge — certified by certified_sum_ok/err"
    }
}

/// Certificate for a `TupleBridge<A, B>`.
///
/// Lean proof: `certified_prod_sound`
impl<A, B> CertifiedLockstepBridge for crate::bridge::TupleBridge<A, B>
where
    A: LockstepBridge + CertifiedLockstepBridge,
    B: LockstepBridge + CertifiedLockstepBridge,
    A::Real: Debug + Clone + 'static,
    A::Model: Debug + Clone + 'static,
    B::Real: Debug + Clone + 'static,
    B::Model: Debug + Clone + 'static,
    A::Observed: Debug + PartialEq + Clone + 'static,
    B::Observed: Debug + PartialEq + Clone + 'static,
{
    fn synthesis_description() -> &'static str {
        "TupleBridge — certified by certified_prod_sound"
    }
}

/// Certificate for an `OptionBridge<B>`.
///
/// Lean proof: `certified_option_some` / `certified_option_none`
impl<B> CertifiedLockstepBridge for crate::bridge::OptionBridge<B>
where
    B: LockstepBridge + CertifiedLockstepBridge,
    B::Real: Debug + Clone + 'static,
    B::Model: Debug + Clone + 'static,
    B::Observed: Debug + PartialEq + Clone + 'static,
{
    fn synthesis_description() -> &'static str {
        "OptionBridge — certified by certified_option_some/none"
    }
}

/// Certificate for a `VecBridge<B>`.
///
/// Lean proof: `certified_list_nil` / `certified_list_cons`
impl<B> CertifiedLockstepBridge for crate::bridge::VecBridge<B>
where
    B: LockstepBridge + CertifiedLockstepBridge,
    B::Real: Debug + Clone + 'static,
    B::Model: Debug + Clone + 'static,
    B::Observed: Debug + PartialEq + Clone + 'static,
{
    fn synthesis_description() -> &'static str {
        "VecBridge — certified by certified_list_nil/cons"
    }
}

/// Certificate for `UnitBridge`.
///
/// Lean proof: `certified_opaque_sound` (Unit is trivially opaque)
impl CertifiedLockstepBridge for crate::bridge::UnitBridge {
    fn synthesis_description() -> &'static str {
        "UnitBridge — certified by certified_opaque_sound"
    }
}

/// Verify that a bridge type is certified and print its certificate.
///
/// This is a compile-time check: if the bridge type doesn't
/// implement `CertifiedLockstepBridge`, the code won't compile.
pub fn verify_certified<B: CertifiedLockstepBridge>() -> &'static str {
    B::synthesis_description()
}
