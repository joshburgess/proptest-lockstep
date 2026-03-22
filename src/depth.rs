//! Bridge-indexed testing depth.
//!
//! Computes the minimum testing depth needed for each action based
//! on its bridge structure. Opaque bridges require deeper testing
//! than transparent ones because wrong opaque handles are only
//! detected when they're USED later (delayed detection).
//!
//! Based on the `opaque_depth_sensitivity` theorem: depth 1 can pass
//! while depth 2 fails for opaque bridges.
//!
//! # Usage
//!
//! ```ignore
//! let depth = recommended_depth::<MyModel>();
//! println!("Recommended testing depth: {}", depth);
//! run_lockstep_test::<MyModel>(1..depth);
//! ```

use crate::bridge::LockstepBridge;

/// Information about bridge depth requirements.
#[derive(Debug, Clone)]
pub struct DepthAnalysis {
    /// Whether the bridge has any opaque components.
    pub has_opaque: bool,
    /// The nesting depth of the bridge (how many lifts deep).
    pub nesting_depth: usize,
    /// Recommended minimum testing depth.
    pub recommended_depth: usize,
}

impl std::fmt::Display for DepthAnalysis {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Bridge depth analysis: opaque={}, nesting={}, recommended_depth={}",
            self.has_opaque, self.nesting_depth, self.recommended_depth,
        )
    }
}

/// Trait for bridges that can report their depth requirements.
pub trait BridgeDepth: LockstepBridge {
    /// Whether this bridge has any opaque components.
    fn has_opaque() -> bool;

    /// The nesting depth of this bridge.
    fn nesting_depth() -> usize;
}

// Implementations for built-in bridges

impl<T: std::fmt::Debug + Clone + PartialEq + 'static> BridgeDepth
    for crate::bridge::Transparent<T>
{
    fn has_opaque() -> bool { false }
    fn nesting_depth() -> usize { 0 }
}

impl<R: 'static, M: 'static> BridgeDepth for crate::bridge::Opaque<R, M> {
    fn has_opaque() -> bool { true }
    fn nesting_depth() -> usize { 0 }
}

impl BridgeDepth for crate::bridge::UnitBridge {
    fn has_opaque() -> bool { false }
    fn nesting_depth() -> usize { 0 }
}

impl<OkB, ErrB> BridgeDepth for crate::bridge::ResultBridge<OkB, ErrB>
where
    OkB: BridgeDepth,
    ErrB: BridgeDepth,
    OkB::Real: std::fmt::Debug + Clone + 'static,
    OkB::Model: std::fmt::Debug + Clone + 'static,
    ErrB::Real: std::fmt::Debug + Clone + 'static,
    ErrB::Model: std::fmt::Debug + Clone + 'static,
    OkB::Observed: std::fmt::Debug + PartialEq + Clone + 'static,
    ErrB::Observed: std::fmt::Debug + PartialEq + Clone + 'static,
{
    fn has_opaque() -> bool { OkB::has_opaque() || ErrB::has_opaque() }
    fn nesting_depth() -> usize { 1 + OkB::nesting_depth().max(ErrB::nesting_depth()) }
}

impl<A, B> BridgeDepth for crate::bridge::TupleBridge<A, B>
where
    A: BridgeDepth,
    B: BridgeDepth,
    A::Real: std::fmt::Debug + Clone + 'static,
    A::Model: std::fmt::Debug + Clone + 'static,
    B::Real: std::fmt::Debug + Clone + 'static,
    B::Model: std::fmt::Debug + Clone + 'static,
    A::Observed: std::fmt::Debug + PartialEq + Clone + 'static,
    B::Observed: std::fmt::Debug + PartialEq + Clone + 'static,
{
    fn has_opaque() -> bool { A::has_opaque() || B::has_opaque() }
    fn nesting_depth() -> usize { 1 + A::nesting_depth().max(B::nesting_depth()) }
}

impl<B> BridgeDepth for crate::bridge::OptionBridge<B>
where
    B: BridgeDepth,
    B::Real: std::fmt::Debug + Clone + 'static,
    B::Model: std::fmt::Debug + Clone + 'static,
    B::Observed: std::fmt::Debug + PartialEq + Clone + 'static,
{
    fn has_opaque() -> bool { B::has_opaque() }
    fn nesting_depth() -> usize { 1 + B::nesting_depth() }
}

impl<B> BridgeDepth for crate::bridge::VecBridge<B>
where
    B: BridgeDepth,
    B::Real: std::fmt::Debug + Clone + 'static,
    B::Model: std::fmt::Debug + Clone + 'static,
    B::Observed: std::fmt::Debug + PartialEq + Clone + 'static,
{
    fn has_opaque() -> bool { B::has_opaque() }
    fn nesting_depth() -> usize { 1 + B::nesting_depth() }
}

/// Analyze a bridge's depth requirements.
pub fn analyze_depth<B: BridgeDepth>() -> DepthAnalysis {
    let has_opaque = B::has_opaque();
    let nesting_depth = B::nesting_depth();

    // Recommended depth:
    // - Transparent-only: depth 1 suffices for single-step detection
    // - With opaque: depth ≥ 2 needed (opaque_depth_sensitivity theorem)
    // - Add nesting_depth as a heuristic for complex bridges
    let recommended_depth = if has_opaque {
        2 + nesting_depth
    } else {
        1 + nesting_depth
    };

    DepthAnalysis {
        has_opaque,
        nesting_depth,
        recommended_depth,
    }
}
