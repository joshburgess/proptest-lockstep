//! Effect-indexed commutativity lattice.
//!
//! Replaces the O(n²) dynamic model oracle (`operations_commute`)
//! with O(1) static effect annotation lookups. Each action declares
//! its **effect footprint** — which resources it reads/writes — and
//! commutativity is determined from the footprints without running
//! the model.
//!
//! Two actions commute iff their effect footprints don't conflict:
//! - Read/Read: always commute (no conflict)
//! - Read/Write on different resources: commute
//! - Write/Write on different resources: commute
//! - Read/Write or Write/Write on the same resource: DON'T commute
//!
//! The dynamic model oracle remains as a **fallback** for actions
//! without effect annotations — graceful degradation, not a breaking
//! change.
//!
//! # Architecture
//!
//! Users implement [`EffectModel`] on top of [`LockstepModel`]:
//! - `Effect` — the effect type (e.g., `KvEffect::Read(key)`)
//! - `effect_of` — extract the effect from an action
//!
//! The [`ConflictAlgebra`] trait defines when two effects conflict.
//! Built-in implementations cover the common read/write pattern.

use std::fmt::Debug;
use std::hash::Hash;

use crate::action::AnyAction;
use crate::model::LockstepModel;

// ---------------------------------------------------------------------------
// Conflict algebra
// ---------------------------------------------------------------------------

/// Determines whether two effects conflict (don't commute).
///
/// Two actions commute iff their effects DON'T conflict. This is
/// the static approximation of the dynamic `operations_commute` check.
pub trait ConflictAlgebra: Debug + Clone {
    /// Returns `true` if these two effects conflict (don't commute).
    fn conflicts_with(&self, other: &Self) -> bool;

    /// Returns `true` if these two effects commute (don't conflict).
    fn commutes_with(&self, other: &Self) -> bool {
        !self.conflicts_with(other)
    }
}

// ---------------------------------------------------------------------------
// Built-in: Read/Write effect on a keyed resource
// ---------------------------------------------------------------------------

/// A read or write effect on a keyed resource.
///
/// This is the most common effect pattern for data structures:
/// operations either read or write, and they're keyed by some
/// resource identifier (key, handle, index, etc.).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ReadWriteEffect<K: Debug + Clone + Eq + Hash> {
    /// Read from a specific resource.
    Read(K),
    /// Write to a specific resource.
    Write(K),
    /// Read from all resources (e.g., `len()`, `iter()`).
    ReadAll,
    /// Write to all resources (e.g., `clear()`).
    WriteAll,
    /// No effect (pure computation).
    None,
}

impl<K: Debug + Clone + Eq + Hash> ConflictAlgebra for ReadWriteEffect<K> {
    fn conflicts_with(&self, other: &Self) -> bool {
        use ReadWriteEffect::*;
        match (self, other) {
            // No effect never conflicts
            (None, _) | (_, None) => false,

            // Read/Read never conflicts
            (Read(_), Read(_)) => false,
            (Read(_), ReadAll) | (ReadAll, Read(_)) => false,
            (ReadAll, ReadAll) => false,

            // Read/Write conflicts on same key
            (Read(k1), Write(k2)) | (Write(k2), Read(k1)) => k1 == k2,

            // Read/WriteAll always conflicts
            (Read(_), WriteAll) | (WriteAll, Read(_)) => true,
            (ReadAll, Write(_)) | (Write(_), ReadAll) => true,
            (ReadAll, WriteAll) | (WriteAll, ReadAll) => true,

            // Write/Write conflicts on same key
            (Write(k1), Write(k2)) => k1 == k2,

            // WriteAll conflicts with everything except None and ReadAll
            (WriteAll, WriteAll) => true,
            (WriteAll, Write(_)) | (Write(_), WriteAll) => true,
        }
    }
}

// ---------------------------------------------------------------------------
// Effect model trait
// ---------------------------------------------------------------------------

/// Extension trait for lockstep models with effect annotations.
///
/// Each action declares its effect footprint. Commutativity is
/// determined by checking whether effects conflict, without running
/// the model in both orderings.
pub trait EffectModel: LockstepModel {
    /// The effect type.
    type Effect: ConflictAlgebra;

    /// Extract the effect from an action.
    ///
    /// Returns `None` if the action has no effect annotation —
    /// the framework falls back to the dynamic model oracle.
    fn effect_of(action: &dyn AnyAction) -> Option<Self::Effect>;
}

// ---------------------------------------------------------------------------
// Static commutativity check
// ---------------------------------------------------------------------------

/// Check whether two actions commute based on their effect annotations.
///
/// Returns:
/// - `Some(true)` — effects don't conflict (commute)
/// - `Some(false)` — effects conflict (don't commute)
/// - `None` — one or both actions have no effect annotation (use
///   dynamic fallback)
pub fn effects_commute<M: EffectModel>(
    a: &dyn AnyAction,
    b: &dyn AnyAction,
) -> Option<bool> {
    let ea = M::effect_of(a)?;
    let eb = M::effect_of(b)?;
    Some(ea.commutes_with(&eb))
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for effect-indexed commutativity.
#[derive(Debug, Clone)]
pub struct EffectConfig {
    /// Whether to validate effect annotations against the dynamic
    /// oracle. When true, the framework checks that `effects_commute`
    /// agrees with `operations_commute` for every pair, and reports
    /// inconsistencies. Default: false (trust annotations).
    pub validate_effects: bool,
}

impl Default for EffectConfig {
    fn default() -> Self {
        EffectConfig {
            validate_effects: false,
        }
    }
}

// ---------------------------------------------------------------------------
// Effect validation
// ---------------------------------------------------------------------------

/// Validate that effect annotations are consistent with the dynamic
/// model oracle. Returns a list of inconsistencies.
///
/// An inconsistency means:
/// - Effects say "commute" but the model says "don't commute"
///   (unsound annotation — could cause DPOR to miss bugs)
/// - Effects say "don't commute" but the model says "commute"
///   (conservative annotation — safe but reduces DPOR effectiveness)
#[derive(Debug, Clone)]
pub struct EffectInconsistency {
    /// Description of action A.
    pub action_a: String,
    /// Description of action B.
    pub action_b: String,
    /// What the effect annotation says.
    pub effect_says_commute: bool,
    /// What the dynamic oracle says.
    pub model_says_commute: bool,
    /// Whether this is unsound (effect says commute but model disagrees).
    pub is_unsound: bool,
}

impl std::fmt::Display for EffectInconsistency {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let severity = if self.is_unsound { "UNSOUND" } else { "conservative" };
        write!(
            f,
            "[{}] {:?} vs {:?}: effects say {}, model says {}",
            severity,
            self.action_a,
            self.action_b,
            if self.effect_says_commute { "commute" } else { "conflict" },
            if self.model_says_commute { "commute" } else { "conflict" },
        )
    }
}
