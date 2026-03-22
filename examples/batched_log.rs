#![allow(dead_code)]
//! Batched append-only log with crash-recovery testing.
//!
//! Unlike the simple WAL example (where every append is immediately
//! durable), this log **buffers writes** and only persists them on
//! explicit `flush()`. A crash between flushes loses the current
//! batch — this is the data-loss window.
//!
//! This is a realistic pattern: databases, message queues, and file
//! systems all batch writes for performance. The crash-recovery
//! framework verifies that:
//! 1. Flushed data survives crashes
//! 2. Unflushed data is correctly lost
//! 3. The system is usable after recovery
//!
//! Demonstrates:
//! - **Batched durability**: writes accumulate in a buffer
//! - **Explicit flush**: `flush()` persists the current batch
//! - **Data-loss window**: crash between flushes loses pending writes
//! - **Crash-recovery verification**: model tracks what's durable
//!
//! Run with: `cargo test --example batched_log`

use std::any::Any;

use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;
use proptest_lockstep::invariant::InvariantModel;
use proptest_lockstep::crash_recovery::{CrashRecoveryModel, CrashRecoveryConfig};

// ============================================================================
// Batched log — SUT
// ============================================================================

/// An append-only log with batched writes.
///
/// `pending` holds writes that haven't been flushed.
/// `durable` holds writes that have been persisted (survive crash).
/// On crash, `pending` is lost and the log recovers from `durable`.
#[derive(Debug)]
struct BatchedLog {
    durable: Vec<String>,
    pending: Vec<String>,
}

impl BatchedLog {
    fn new() -> Self {
        BatchedLog {
            durable: Vec::new(),
            pending: Vec::new(),
        }
    }

    /// Append an entry to the pending buffer (NOT durable yet).
    fn append(&mut self, entry: &str) {
        self.pending.push(entry.to_string());
    }

    /// Flush pending writes to durable storage.
    /// After flush, all pending entries are persisted.
    fn flush(&mut self) -> usize {
        let flushed = self.pending.len();
        self.durable.append(&mut self.pending);
        flushed
    }

    /// Read from durable + pending (full view).
    fn read(&self, index: usize) -> Option<String> {
        if index < self.durable.len() {
            self.durable.get(index).cloned()
        } else {
            self.pending.get(index - self.durable.len()).cloned()
        }
    }

    /// Total entries (durable + pending).
    fn len(&self) -> usize {
        self.durable.len() + self.pending.len()
    }

    /// Number of entries that would survive a crash.
    fn durable_len(&self) -> usize {
        self.durable.len()
    }

    /// Number of entries that would be LOST on crash.
    fn pending_len(&self) -> usize {
        self.pending.len()
    }

    /// Simulate crash recovery: lose pending, keep durable.
    fn recover(self) -> Self {
        BatchedLog {
            durable: self.durable,
            pending: Vec::new(), // lost!
        }
    }
}

// ============================================================================
// Model — tracks both durable and total state
// ============================================================================

/// The model tracks the full log (all appends) AND the durable
/// prefix (what survives a crash). After flush, the durable prefix
/// catches up to the full log.
#[derive(Debug, Clone, PartialEq)]
struct LogModel {
    /// All entries (durable + pending). This is what reads see.
    all_entries: Vec<String>,
    /// The durable prefix length. Entries [0..durable_len) survive crash.
    durable_len: usize,
}

impl LogModel {
    fn new() -> Self {
        LogModel {
            all_entries: Vec::new(),
            durable_len: 0,
        }
    }
}

// ============================================================================
// Actions
// ============================================================================

#[proptest_lockstep::lockstep_actions(state = LogModel)]
pub mod blog {
    #[action(real_return = "()")]
    pub struct Append {
        pub entry: String,
    }

    /// Flush returns the number of entries flushed.
    #[action(real_return = "usize")]
    pub struct Flush;

    #[action(real_return = "Option<String>")]
    pub struct Read {
        pub index: usize,
    }

    #[action(real_return = "usize")]
    pub struct Len;

    /// How many entries are durable (survive crash).
    #[action(real_return = "usize")]
    pub struct DurableLen;

    /// How many entries are pending (lost on crash).
    #[action(real_return = "usize")]
    pub struct PendingLen;
}

// ============================================================================
// Interpreters
// ============================================================================

#[derive(Debug, Clone)]
struct BatchedLogLockstep;

impl blog::BlogModelInterp for BatchedLogLockstep {
    type State = LogModel;

    fn append(s: &mut LogModel, a: &blog::Append, _: &TypedEnv) {
        s.all_entries.push(a.entry.clone());
    }

    fn flush(s: &mut LogModel, _: &blog::Flush, _: &TypedEnv) -> usize {
        let pending = s.all_entries.len() - s.durable_len;
        s.durable_len = s.all_entries.len();
        pending
    }

    fn read(s: &mut LogModel, a: &blog::Read, _: &TypedEnv) -> Option<String> {
        s.all_entries.get(a.index).cloned()
    }

    fn len(s: &mut LogModel, _: &blog::Len, _: &TypedEnv) -> usize {
        s.all_entries.len()
    }

    fn durable_len(s: &mut LogModel, _: &blog::DurableLen, _: &TypedEnv) -> usize {
        s.durable_len
    }

    fn pending_len(s: &mut LogModel, _: &blog::PendingLen, _: &TypedEnv) -> usize {
        s.all_entries.len() - s.durable_len
    }
}

impl blog::BlogSutInterp for BatchedLogLockstep {
    type Sut = BatchedLog;

    fn append(s: &mut BatchedLog, a: &blog::Append, _: &TypedEnv) {
        s.append(&a.entry);
    }

    fn flush(s: &mut BatchedLog, _: &blog::Flush, _: &TypedEnv) -> usize {
        s.flush()
    }

    fn read(s: &mut BatchedLog, a: &blog::Read, _: &TypedEnv) -> Option<String> {
        s.read(a.index)
    }

    fn len(s: &mut BatchedLog, _: &blog::Len, _: &TypedEnv) -> usize {
        s.len()
    }

    fn durable_len(s: &mut BatchedLog, _: &blog::DurableLen, _: &TypedEnv) -> usize {
        s.durable_len()
    }

    fn pending_len(s: &mut BatchedLog, _: &blog::PendingLen, _: &TypedEnv) -> usize {
        s.pending_len()
    }
}

// ============================================================================
// LockstepModel
// ============================================================================

impl LockstepModel for BatchedLogLockstep {
    type ModelState = LogModel;
    type Sut = BatchedLog;

    fn init_model() -> LogModel { LogModel::new() }
    fn init_sut() -> BatchedLog { BatchedLog::new() }

    fn gen_action(state: &LogModel, _: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        let entries = vec!["entry_a", "entry_b", "entry_c"];
        let len = state.all_entries.len();

        let mut strats: Vec<BoxedStrategy<Box<dyn AnyAction>>> = vec![
            // Append
            proptest::sample::select(entries)
                .prop_map(|e| blog::append(blog::Append { entry: e.to_string() }))
                .boxed(),
            // Flush
            Just(blog::flush(blog::Flush)).boxed(),
            // Query
            Just(blog::len(blog::Len)).boxed(),
            Just(blog::durable_len(blog::DurableLen)).boxed(),
            Just(blog::pending_len(blog::PendingLen)).boxed(),
        ];

        // Read from valid and slightly-out-of-range indices
        let max_idx = if len > 0 { len + 1 } else { 2 };
        strats.push(
            (0..max_idx)
                .prop_map(|i| blog::read(blog::Read { index: i }))
                .boxed(),
        );

        proptest::strategy::Union::new(strats).boxed()
    }

    fn step_model(s: &mut LogModel, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        blog::dispatch_model::<BatchedLogLockstep>(s, a, e)
    }

    fn step_sut(s: &mut BatchedLog, a: &dyn AnyAction, e: &TypedEnv) -> Box<dyn Any> {
        blog::dispatch_sut::<BatchedLogLockstep>(s, a, e)
    }
}

// ============================================================================
// InvariantModel
// ============================================================================

impl InvariantModel for BatchedLogLockstep {
    fn invariant(state: &LogModel) -> bool {
        // Durable prefix can't exceed total entries
        state.durable_len <= state.all_entries.len()
    }
}

// ============================================================================
// CrashRecoveryModel
// ============================================================================

/// The durable state is the entries that have been flushed.
#[derive(Debug, Clone)]
struct DurableLogState {
    entries: Vec<String>,
}

impl CrashRecoveryModel for BatchedLogLockstep {
    type DurableState = DurableLogState;

    fn model_checkpoint(state: &LogModel) -> DurableLogState {
        DurableLogState {
            entries: state.all_entries[..state.durable_len].to_vec(),
        }
    }

    fn model_recover(checkpoint: &DurableLogState) -> LogModel {
        LogModel {
            all_entries: checkpoint.entries.clone(),
            durable_len: checkpoint.entries.len(),
        }
    }

    fn sut_recover(sut: BatchedLog) -> BatchedLog {
        sut.recover()
    }
}

fn main() {
    println!("Run with `cargo test --example batched_log`");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Sequential lockstep: batched log matches model.
    #[test]
    fn lockstep_batched_log() {
        proptest_lockstep::runner::run_lockstep_test::<BatchedLogLockstep>(1..30);
    }

    /// Crash-recovery: after crash, only flushed entries survive.
    /// Pending (unflushed) entries are correctly lost.
    #[test]
    fn crash_recovery_batched_log() {
        proptest_lockstep::crash_recovery::run_crash_recovery_test::<BatchedLogLockstep>(
            CrashRecoveryConfig {
                crash_probability: 0.15,
                max_crashes: 5,
                cases: 200,
                min_ops: 5,
                max_ops: 30,
            },
        );
    }

    /// High crash frequency: stress the flush/crash interaction.
    /// Many crashes between flushes tests that unflushed data is
    /// consistently lost and the log remains usable.
    #[test]
    fn crash_recovery_high_frequency() {
        proptest_lockstep::crash_recovery::run_crash_recovery_test::<BatchedLogLockstep>(
            CrashRecoveryConfig {
                crash_probability: 0.3,
                max_crashes: 10,
                cases: 100,
                min_ops: 10,
                max_ops: 40,
            },
        );
    }
}
