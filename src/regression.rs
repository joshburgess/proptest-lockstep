//! Cross-consistency regression detection.
//!
//! Detects when a code change causes a system to drop from a stronger
//! consistency level to a weaker one. Compares the consistency of two
//! `LockstepModel` implementations (e.g., version N vs version N+1)
//! and reports regressions.
//!
//! # Use Cases
//!
//! - **CI integration**: fail the build if a PR drops linearizability
//! - **Version comparison**: compare consistency across releases
//! - **Refactoring safety**: verify refactors don't weaken guarantees
//!
//! # Example
//!
//! ```ignore
//! let before = classify_consistency::<V1Model>(config.clone());
//! let after = classify_consistency::<V2Model>(config);
//! let regression = check_regression(&before, &after);
//! if regression.is_regression {
//!     panic!("Consistency regression: {} → {}", before.level, after.level);
//! }
//! ```

use std::fmt;

use crate::classify::{ClassifyResult, ConsistencyLevel};

/// Result of a consistency regression check.
#[derive(Debug, Clone)]
pub struct RegressionResult {
    /// Whether a regression was detected.
    pub is_regression: bool,
    /// The consistency level before the change.
    pub before: ConsistencyLevel,
    /// The consistency level after the change.
    pub after: ConsistencyLevel,
    /// Number of NEW mismatches introduced by the change.
    pub new_mismatches: usize,
}

impl fmt::Display for RegressionResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_regression {
            write!(
                f,
                "REGRESSION: {} → {} ({} new mismatches)",
                self.before, self.after, self.new_mismatches,
            )
        } else if self.before == self.after {
            write!(f, "No change: {}", self.before)
        } else {
            write!(
                f,
                "IMPROVEMENT: {} → {}",
                self.before, self.after,
            )
        }
    }
}

/// Check for a consistency regression between two classification results.
///
/// A regression occurs when the "after" result has a weaker consistency
/// level than the "before" result (e.g., linearizable → weaker).
pub fn check_regression(
    before: &ClassifyResult,
    after: &ClassifyResult,
) -> RegressionResult {
    let is_regression = after.level < before.level
        || (after.level == before.level && after.mismatches_found > before.mismatches_found);

    let new_mismatches = after.mismatches_found.saturating_sub(before.mismatches_found);

    RegressionResult {
        is_regression,
        before: before.level,
        after: after.level,
        new_mismatches,
    }
}

/// Assert no consistency regression occurred.
///
/// Panics with a detailed message if the "after" classification is
/// weaker than the "before" classification.
pub fn assert_no_regression(
    before: &ClassifyResult,
    after: &ClassifyResult,
) {
    let result = check_regression(before, after);
    if result.is_regression {
        panic!(
            "Consistency regression detected!\n\
             Before: {} ({} traces, {} mismatches)\n\
             After:  {} ({} traces, {} mismatches)\n\
             {}",
            before.level, before.traces_tested, before.mismatches_found,
            after.level, after.traces_tested, after.mismatches_found,
            result,
        );
    }
}
