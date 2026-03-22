#![allow(dead_code)]
//! Write-ahead log crash-recovery test.
//!
//! Tests a write-ahead log (WAL) with crash-recovery semantics.
//! The SUT maintains an in-memory buffer that is "flushed" (persisted)
//! on each append. On crash, the SUT recovers from the persisted log,
//! losing any un-flushed state.
//!
//! This is the canonical crash-recovery example: a log that must
//! survive crashes without losing committed entries.
//!
//! Demonstrates:
//! - **Crash-recovery testing**: random crash injection between operations
//! - **Durable state tracking**: model checkpoints what should survive
//! - **Recovery verification**: after crash, SUT matches model's expectation
//! - **State invariants**: log length is always consistent
//!
//! Run with: `cargo test --example crash_recovery_log`

use std::any::Any;

use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;
use proptest_lockstep::invariant::InvariantModel;
use proptest_lockstep::crash_recovery::{CrashRecoveryModel, CrashRecoveryConfig};

// ============================================================================
// Write-ahead log — SUT
// ============================================================================

/// A write-ahead log with simulated persistence.
///
/// `committed` represents on-disk entries (survive crash).
/// `pending` represents in-memory entries not yet flushed.
///
/// In this implementation, `append` immediately commits (synchronous
/// flush). A more interesting variant could buffer writes and flush
/// lazily, creating a window for data loss.
#[derive(Debug)]
struct WriteAheadLog {
    /// Entries that have been "fsynced" — survive crash.
    committed: Vec<String>,
    /// Total reads served (including from committed entries).
    read_count: usize,
}

impl WriteAheadLog {
    fn new() -> Self {
        WriteAheadLog {
            committed: Vec::new(),
            read_count: 0,
        }
    }

    fn append(&mut self, entry: &str) -> usize {
        self.committed.push(entry.to_string());
        self.committed.len() - 1 // return index
    }

    fn read(&mut self, index: usize) -> Option<String> {
        self.read_count += 1;
        self.committed.get(index).cloned()
    }

    fn len(&self) -> usize {
        self.committed.len()
    }

    /// Simulate crash recovery: reconstruct from "disk" (committed entries).
    /// In-memory state (read_count) is lost.
    fn recover(self) -> Self {
        WriteAheadLog {
            committed: self.committed, // "disk" survives
            read_count: 0,             // in-memory state lost
        }
    }
}

// ============================================================================
// Model — sequential log
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
struct LogModel {
    entries: Vec<String>,
}

impl LogModel {
    fn new() -> Self {
        LogModel {
            entries: Vec::new(),
        }
    }
}

// ============================================================================
// Actions
// ============================================================================

#[proptest_lockstep::lockstep_actions(state = LogModel)]
pub mod wal {
    // Returns the index of the appended entry.
    // Bridge: Transparent<usize>
    #[action(real_return = "usize")]
    pub struct Append {
        pub entry: String,
    }

    // Returns the entry at the given index, or None.
    // Bridge: OptionBridge<Transparent<String>>
    #[action(real_return = "Option<String>")]
    pub struct Read {
        pub index: usize,
    }

    // Bridge: Transparent<usize>
    #[action(real_return = "usize")]
    pub struct Len;
}

// ============================================================================
// Interpreters
// ============================================================================

#[derive(Debug, Clone)]
struct WalLockstep;

impl wal::WalModelInterp for WalLockstep {
    type State = LogModel;

    fn append(s: &mut LogModel, a: &wal::Append, _: &TypedEnv) -> usize {
        s.entries.push(a.entry.clone());
        s.entries.len() - 1
    }

    fn read(s: &mut LogModel, a: &wal::Read, _: &TypedEnv) -> Option<String> {
        s.entries.get(a.index).cloned()
    }

    fn len(s: &mut LogModel, _: &wal::Len, _: &TypedEnv) -> usize {
        s.entries.len()
    }
}

impl wal::WalSutInterp for WalLockstep {
    type Sut = WriteAheadLog;

    fn append(s: &mut WriteAheadLog, a: &wal::Append, _: &TypedEnv) -> usize {
        s.append(&a.entry)
    }

    fn read(s: &mut WriteAheadLog, a: &wal::Read, _: &TypedEnv) -> Option<String> {
        s.read(a.index)
    }

    fn len(s: &mut WriteAheadLog, _: &wal::Len, _: &TypedEnv) -> usize {
        s.len()
    }
}

// ============================================================================
// LockstepModel
// ============================================================================

impl LockstepModel for WalLockstep {
    type ModelState = LogModel;
    type Sut = WriteAheadLog;

    fn init_model() -> LogModel {
        LogModel::new()
    }
    fn init_sut() -> WriteAheadLog {
        WriteAheadLog::new()
    }

    fn gen_action(state: &LogModel, _env: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        let entries = vec!["entry_a", "entry_b", "entry_c", "entry_d"];
        let len = state.entries.len();

        let mut strats: Vec<BoxedStrategy<Box<dyn AnyAction>>> = vec![
            // Append a new entry
            proptest::sample::select(entries)
                .prop_map(|e| wal::append(wal::Append { entry: e.to_string() }))
                .boxed(),
            // Check length
            Just(wal::len(wal::Len)).boxed(),
        ];

        // Read from valid indices (and occasionally invalid ones)
        if len > 0 {
            strats.push(
                (0..len + 2)
                    .prop_map(|i| wal::read(wal::Read { index: i }))
                    .boxed(),
            );
        } else {
            strats.push(
                (0usize..3)
                    .prop_map(|i| wal::read(wal::Read { index: i }))
                    .boxed(),
            );
        }

        proptest::strategy::Union::new(strats).boxed()
    }

    fn step_model(state: &mut LogModel, action: &dyn AnyAction, env: &TypedEnv) -> Box<dyn Any> {
        wal::dispatch_model::<WalLockstep>(state, action, env)
    }

    fn step_sut(
        sut: &mut WriteAheadLog,
        action: &dyn AnyAction,
        env: &TypedEnv,
    ) -> Box<dyn Any> {
        wal::dispatch_sut::<WalLockstep>(sut, action, env)
    }
}

// ============================================================================
// InvariantModel — shared state invariant
// ============================================================================

impl InvariantModel for WalLockstep {
    fn invariant(state: &LogModel) -> bool {
        // Invariant: log entries are never empty strings
        // (our generators only produce non-empty strings)
        state.entries.iter().all(|e| !e.is_empty())
    }
}

// ============================================================================
// CrashRecoveryModel — crash/recovery semantics
// ============================================================================

impl CrashRecoveryModel for WalLockstep {
    /// The durable state is the committed log entries.
    type DurableState = Vec<String>;

    fn model_checkpoint(state: &LogModel) -> Vec<String> {
        state.entries.clone()
    }

    fn model_recover(checkpoint: &Vec<String>) -> LogModel {
        LogModel {
            entries: checkpoint.clone(),
        }
    }

    fn sut_recover(sut: WriteAheadLog) -> WriteAheadLog {
        sut.recover()
    }
}

fn main() {
    println!("Run with `cargo test --example crash_recovery_log`");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Sequential lockstep test (no crashes).
    #[test]
    fn lockstep_wal() {
        proptest_lockstep::runner::run_lockstep_test::<WalLockstep>(1..30);
    }

    /// Crash-recovery test: random crash injection.
    /// Verifies that after each crash, the log recovers correctly
    /// and subsequent operations produce correct results.
    #[test]
    fn crash_recovery_wal() {
        proptest_lockstep::crash_recovery::run_crash_recovery_test::<WalLockstep>(
            CrashRecoveryConfig {
                crash_probability: 0.15,
                max_crashes: 5,
                cases: 200,
                min_ops: 5,
                max_ops: 30,
            },
        );
    }

    /// High crash frequency: stress test recovery logic.
    #[test]
    fn crash_recovery_wal_high_frequency() {
        proptest_lockstep::crash_recovery::run_crash_recovery_test::<WalLockstep>(
            CrashRecoveryConfig {
                crash_probability: 0.4,
                max_crashes: 10,
                cases: 100,
                min_ops: 10,
                max_ops: 40,
            },
        );
    }
}
