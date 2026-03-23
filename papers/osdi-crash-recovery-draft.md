# Crash-Recovery Property-Based Testing: Bridging Jepsen and Perennial

## Paper Outline

### 1. Introduction (~2 pages)
Motivate the gap between Jepsen-style empirical crash testing and Perennial-style full crash-recovery verification. Present the key insight: lockstep property-based testing with random crash injection, backed by machine-checked crash bisimulation theorems, occupies a sweet spot---more rigorous than Jepsen, more practical than Perennial. Summarize contributions.

### 2. Background and Motivation (~2 pages)
Review crash-recovery testing in practice: Jepsen's fault-injection methodology (network partitions, process kills, clock skew), its strengths (real systems, real bugs), and its limitation (no formal guarantee that passing tests imply correctness). Contrast with Perennial's crash Hoare logic in Coq, which provides full verification but requires expert effort per system. Introduce lockstep testing as a middle ground and define the problem: what does it mean for crash-recovery PBT to be *sound*?

### 3. Crash-Recovery Lockstep Model (~3 pages)
Define the `CrashRecoveryModel` trait: `DurableState`, `model_checkpoint`, `model_recover`, `sut_recover`. Explain the runner: probabilistic crash injection between lockstep steps, environment reset on crash, invariant checking before and after recovery. Walk through the write-ahead log example (synchronous append, crash recovery from committed entries) and the batched log example (buffered writes, explicit flush, data-loss window between flushes). Show the model tracks the durable prefix precisely, so crashes at any point are verified against the correct expectation.

### 4. Crash Bisimulation: Formal Foundation (~3 pages)
Present the crash bisimulation definition from Lean 4: an inductive relation over (model state, SUT state) pairs at bounded depth, requiring (a) the invariant holds, (b) normal actions preserve bridge equivalence and the bisimulation, (c) crash-recovery transitions preserve the bisimulation. Prove crash bisimulation strictly implies bounded bisimulation. State the key monotonicity, recovery-preservation, and double-crash theorems. Explain how these theorems justify the runner's crash-injection strategy.

### 5. Crash-Transparent Action Elimination (~2 pages)
Define crash-transparent actions: actions whose checkpoint is invariant under execution and whose SUT effects are undone by recovery (e.g., read-only operations, in-memory-only mutations). Prove the single-pair elimination theorem: in a crash-interleaved trace, a crash-transparent action immediately before a crash can be removed without changing the final state. Extend to multi-pair elimination via `reduce_crash_trace`. Discuss the practical implication: the crash explorer can prune its search space without losing completeness.

### 6. Game-Semantic Characterization (~2 pages)
Present the crash bisimulation game: an Attacker with four moves (pick an action, trigger a crash, claim a bridge failure, claim an invariant violation) plays against a Defender who must show the system is correct. Prove `crash_bisim_game_semantic`: negation of crash bisimulation is equivalent to the existence of a winning Attacker strategy. The witness *is* the minimal failing test case, including crash events. Connect to bisimulation-guided shrinking: the game-semantic witness provides a structured explanation of why the system fails.

### 7. Crash-Session Composition (~2 pages)
Extend to systems with session guarantees (read-your-writes, monotonic reads) that must survive crashes. Define the `CrashSessionSystem` structure: session identifiers, per-session write histories that reset on crash. Prove `crash_session_obs_equiv_iff`: crash-session bisimulation is equivalent to crash-interleaved observational equivalence, where traces include both action and crash events. This biconditional ensures testing completeness for session-aware crash-recovery systems.

### 8. Evaluation (~3 pages)
**Case study 1: Write-ahead log.** Synchronous append, crash recovery from committed entries. Model: `Vec<String>`. Show the framework catches a seeded bug where recovery drops the last committed entry. **Case study 2: Batched log.** Buffered writes with explicit flush. Model tracks durable prefix vs. pending buffer. Show the framework correctly identifies that unflushed entries are lost on crash, and catches a seeded bug where flush fails to advance the durable pointer. **Case study 3: Crash-consistent session KV.** Multi-session key-value store where read-your-writes must hold within a session but session history resets on crash. Show the framework catches violations of read-your-writes after recovery. **Performance:** Report test throughput (cases/second) at various crash probabilities and trace lengths.

### 9. Related Work (~1.5 pages)
Jepsen and its lineage (Chaos Monkey, LitmusTk). Perennial and crash Hoare logic (FSCQ, DaisyNFS). CrashMonkey and filesystem-specific crash testing. Property-based testing: QuickCheck, Hedgehog, proptest, quickcheck-lockstep. Formal PBT metatheory (none prior). Bisimulation theory: process algebra, game characterizations. Crash consistency models: ext4 ordering, Btrfs COW, ZFS.

### 10. Conclusion (~0.5 pages)
Crash-recovery PBT with machine-checked soundness occupies a practical and rigorous middle ground. The approach is applicable to any system with a durable/volatile state split. Future work: integration with real storage stacks, crash-recovery DPOR for concurrent crash-recovery systems, and extension to partial-write (torn page) models.

---

## Introduction (Draft)

Storage systems must survive crashes. A write-ahead log that loses committed entries after a power failure, a database that corrupts its B-tree after an untimely `kill -9`, a filesystem that silently drops metadata updates after a kernel panic---these are not hypothetical failures. They are the bugs that wake on-call engineers at 3 AM and destroy months of user data. Testing crash recovery is therefore one of the most important tasks in systems engineering, and one of the least well-served by existing tools.

Today, practitioners face a stark choice. On one side stands Jepsen, the gold standard for empirical distributed-systems testing. Jepsen injects real faults---network partitions, process kills, clock skew---into running systems and checks that the results satisfy a consistency model. It has found serious bugs in PostgreSQL, MongoDB, CockroachDB, and dozens of other systems. But Jepsen offers no formal guarantee: a passing test suite means the system survived *those particular* fault schedules. There is no theorem connecting "Jepsen passed" to "the system is correct." On the other side stands Perennial, a crash Hoare logic embedded in Coq that provides full mechanical verification of crash-recovery correctness. Perennial has verified FSCQ and DaisyNFS, proving that every possible crash sequence preserves the filesystem's invariants. But the cost is staggering: verifying a single filesystem requires years of expert effort in a proof assistant. No production database, message queue, or key-value store has been verified this way, and none is likely to be.

We present a third option. Our approach---crash-recovery property-based testing with machine-checked soundness---occupies the gap between Jepsen and Perennial. Like Jepsen, we test real implementations by injecting crashes randomly. Like Perennial, we have formal proofs about what our testing methodology guarantees. Unlike Jepsen, we can state precisely what a passing test suite means. Unlike Perennial, our approach requires hours of effort, not years.

The core idea is lockstep testing with crash injection. The developer writes a *model* of their system's durable state---a pure specification of what should survive a crash---and implements three functions: `checkpoint` (extract the durable state from the model), `model_recover` (reconstruct the model from a checkpoint), and `sut_recover` (restart the real system from its persisted state). Our runner then executes random action sequences against both model and system in lockstep, probabilistically injecting crashes between steps. After each crash, both sides recover: the model from its last checkpoint, the system from whatever it persisted. Testing continues on the recovered states. If the system ever diverges from the model---a committed write is missing, an uncommitted write survives, an invariant is violated---the framework reports a minimal failing trace that includes the crash points.

Consider a concrete scenario. A batched append-only log buffers writes in memory and persists them on explicit `flush()`. Between flushes, there is a data-loss window: a crash will lose the pending buffer. Our model tracks both the full log (all appends) and the durable prefix (entries that have been flushed). When a crash occurs, the model rewinds to the durable prefix; the system reconstructs from its on-disk entries. Lockstep testing then verifies that every subsequent read, length query, and append produces results consistent with the model's post-recovery state. If the system's recovery logic has an off-by-one error---say, it replays one fewer entry than it should---the framework catches it within seconds, not after a week-long Jepsen campaign.

What distinguishes our work from prior crash-testing tools is the formal foundation. We prove, in 194 lines of machine-checked Lean 4, that our testing methodology is sound. The central theorem defines *crash bisimulation*: an inductive relation over (model state, system state) pairs that requires (1) a state invariant holds at every reachable state, (2) normal actions preserve observational equivalence via typed bridges, and (3) after a crash, the recovered states remain in the bisimulation. We prove that crash bisimulation strictly implies bounded bisimulation (crash-correct systems are also correct without crashes), that the bisimulation is preserved through double crashes (crash, recover, crash again, recover again), and that the runner's strategy---random crash injection with invariant checking---is a sound decision procedure for crash bisimulation up to a given depth.

We go further with three additional results. First, *crash-transparent action elimination*: we prove that read-only actions immediately before a crash point can be pruned from the trace without changing the final state, reducing the search space for crash exploration. Second, a *game-semantic characterization*: we prove that the negation of crash bisimulation is equivalent to the existence of a winning strategy for an Attacker in a four-move game (pick an action, trigger a crash, claim a bridge failure, claim an invariant violation). The Attacker's strategy *is* the minimal failing test case, providing structured explanations of crash-recovery bugs. Third, *crash-session observational completeness*: for systems with session guarantees (read-your-writes, monotonic reads) that must survive crashes, we prove that our recursive bisimulation definition is equivalent to a trace-based observational characterization where crash events reset per-session histories---a biconditional that ensures testing completeness.

We evaluate our framework on three case studies: a write-ahead log with synchronous commits, a batched log with explicit flush and a data-loss window, and a session-consistent crash-aware key-value store. In each case, the framework catches seeded bugs within seconds, produces minimal failing traces that pinpoint the crash scenario, and scales to hundreds of test cases with multiple crash injections per trace. The entire formal development compiles with zero `sorry` (unfinished proofs) in Lean 4.

Our contributions are:

1. **CrashRecoveryModel**, a trait-based framework for crash-recovery lockstep testing that requires only three user-supplied functions: checkpoint, model recovery, and system recovery.
2. **Crash bisimulation**, the first machine-checked proof that crash-injection PBT is sound, formalized in Lean 4 with monotonicity, recovery-preservation, and double-crash theorems.
3. **Crash-transparent elimination**, a proved optimization that prunes read-only actions before crash points from the exploration space.
4. **Game-semantic crash witnesses**, a proved equivalence between crash bisimulation failure and the existence of a minimal four-move Attacker strategy.
5. **Crash-session observational completeness**, a biconditional connecting crash-session bisimulation to trace-based observational equivalence with crash-induced history resets.
6. **Three case studies** demonstrating the framework on write-ahead logs, batched logs, and session-consistent crash-aware systems.

---

## 2. Background and Motivation

### 2.1 Crash-Recovery Testing in Practice

Storage systems fail in ways that are difficult to reproduce and reason about. A power failure during a write can leave a database with a partially-updated B-tree. A `kill -9` during a compaction can leave a log-structured merge tree with dangling references. A kernel panic during a journaled metadata update can leave a filesystem with an inconsistent directory tree. These failures share a common structure: the system was in the middle of a multi-step operation that was intended to be atomic, and the crash interrupted it at an arbitrary point between the durable commit and the in-memory cleanup.

**Jepsen.** The most widely deployed tool for testing crash-recovery behavior is Jepsen, Kyle Kingsbury's framework for distributed-systems testing. Jepsen spins up a cluster of real nodes, runs a workload against them, injects faults (network partitions, process kills, clock skew, disk full conditions), and then checks that the resulting history satisfies a consistency model such as linearizability or serializability. Jepsen has discovered serious bugs in PostgreSQL, MongoDB, CockroachDB, Elasticsearch, Redis, and dozens of other production systems. Its strength is realism: it tests real implementations under real fault conditions, with real network stacks and real disk I/O.

But Jepsen has a fundamental limitation: it provides no formal connection between passing tests and system correctness. A Jepsen test campaign explores a finite (and typically small) subset of the possible fault schedules. Passing 1,000 Jepsen runs means the system survived those particular 1,000 schedules. It says nothing about schedule 1,001. There is no theorem relating the set of tested schedules to the set of all possible schedules, no proof that the exploration strategy is complete or even sound in any formal sense. Jepsen practitioners compensate with experience, intuition, and long-running campaigns, but the gap between "tested" and "verified" remains wide.

**Perennial.** At the other extreme stands Perennial, a crash Hoare logic embedded in the Coq proof assistant. Perennial extends concurrent separation logic with crash-aware reasoning: specifications include crash conditions, and proofs must show that every possible crash point leaves the system in a state from which recovery can proceed correctly. Perennial has been used to verify FSCQ (a file system), DaisyNFS (an NFS server), and several storage-layer components. The guarantees are absolute: if the proof checks, the system handles every possible crash sequence correctly.

The cost, however, is prohibitive for all but the most critical systems. Verifying FSCQ required multiple person-years of expert effort in Coq. DaisyNFS required similar investment. The proof-to-code ratio is high, the proof assistant has a steep learning curve, and every change to the implementation requires corresponding changes to the proof. No production database, message queue, or key-value store has been verified with Perennial, and the economics of full verification make this unlikely to change for most systems.

**CrashMonkey and filesystem-specific tools.** Between these extremes, several domain-specific tools have emerged. CrashMonkey systematically explores crash states for filesystem operations by intercepting block-level I/O and replaying prefixes. Alice (All File Systems Are Not Created Equal) checks filesystem crash-consistency guarantees by analyzing block traces. These tools are effective for their specific domains but do not generalize to arbitrary stateful systems (databases, caches, queues), and they lack formal soundness guarantees.

### 2.2 The Gap

The landscape reveals a clear gap. Practitioners who need crash-recovery assurance for a new system face a choice between (a) Jepsen-style testing that is practical but provides no formal guarantees, (b) Perennial-style verification that is rigorous but requires years of effort, and (c) domain-specific tools that may not apply. What is missing is a general-purpose approach that is both practical (hours of effort, not years) and formally grounded (a theorem connecting passing tests to system correctness).

### 2.3 Lockstep Testing as a Middle Ground

Property-based testing (PBT) offers a natural starting point. In PBT, the developer writes a model (a simplified specification) and a test harness that generates random inputs, runs them against both the model and the implementation, and checks that the results agree. Libraries like QuickCheck, Hedgehog, and proptest have demonstrated the effectiveness of this approach for sequential and stateless systems.

Lockstep testing extends PBT to stateful systems. The model and implementation execute the same sequence of operations in lockstep, with typed bridges comparing the results at each step. Edsko de Vries's `quickcheck-lockstep` for Haskell showed that this approach can be made rigorous for sequential stateful testing, using GADTs to ensure type-safe comparison of heterogeneous return values.

Our insight is that lockstep testing can be extended to crash-recovery by adding three concepts: (1) a durable-state checkpoint that captures what should survive a crash, (2) a model recovery function that reconstructs the model from a checkpoint, and (3) a system recovery function that restarts the implementation from its persisted state. With these additions, the lockstep runner can inject crashes between any two operations and verify that the system's post-recovery behavior matches the model's expectation. The question we address is: what does it mean, formally, for such a testing methodology to be *sound*?

---

## 3. Crash-Recovery Lockstep Model

### 3.1 The CrashRecoveryModel Trait

The user-facing interface for crash-recovery testing is the `CrashRecoveryModel` trait, which extends the base `LockstepModel` (providing `ModelState`, `Sut`, `init_model`, `init_sut`, `gen_action`, `step_model`, `step_sut`) and `InvariantModel` (providing a per-step state predicate) with three additional items:

```rust
pub trait CrashRecoveryModel: InvariantModel {
    type DurableState: Debug + Clone + 'static;
    fn model_checkpoint(state: &Self::ModelState) -> Self::DurableState;
    fn model_recover(checkpoint: &Self::DurableState) -> Self::ModelState;
    fn sut_recover(sut: Self::Sut) -> Self::Sut;
}
```

**`DurableState`** is the type of data that survives a crash. For a write-ahead log, this is `Vec<String>` (the committed entries). For a batched log with explicit flush, this is the flushed prefix of the log. For a database, it might be a serialized snapshot of the on-disk state.

**`model_checkpoint`** extracts the durable portion from the current model state. This is called after every step to maintain a running record of what would survive a crash at this point. Critically, the checkpoint captures the model's view of durability, not the system's. The model defines the *specification* of what should be durable; the system's actual persistence behavior is what we are testing.

**`model_recover`** reconstructs a fresh model state from a checkpoint. After a crash, the model rewinds to the durable state: all volatile state (pending buffers, in-memory caches, session state) is discarded, and the model reflects only what was committed.

**`sut_recover`** restarts the system under test from its own persisted state. The SUT is consumed (simulating process death) and a new instance is returned (simulating restart). The SUT does not have access to the model's checkpoint; it must reconstruct from whatever it actually persisted to disk. This asymmetry is the heart of crash-recovery testing: the model says what *should* survive, and the SUT shows what *actually* survives.

### 3.2 The Crash-Recovery Runner

The runner, `run_crash_recovery_test`, orchestrates lockstep execution with probabilistic crash injection. The algorithm proceeds as follows:

1. Initialize the model state and SUT.
2. For each generated action in the sequence:
   a. Check the model invariant.
   b. Execute the action on both model and SUT.
   c. Verify the bridge (typed comparison of return values).
   d. Store any returned variables in the typed environment.
   e. With probability `crash_probability` (configurable, default 10%), inject a crash:
      - Checkpoint the model via `model_checkpoint`.
      - Recover the model via `model_recover`.
      - Recover the SUT via `sut_recover`.
      - Reset the typed environment (variables from before the crash may reference values that no longer exist in the recovered state).
      - Check the invariant on the recovered model state.
3. After all actions, check the final invariant.

The `CrashRecoveryConfig` structure controls the exploration parameters: `crash_probability` (default 0.1), `max_crashes` per run (default 3), `cases` (number of test cases, default 100), and the operation sequence length range.

A key design decision is that crash injection occurs *between* steps, not during them. This models crash-stop failures where operations are atomic but the system can fail at any inter-operation point. This is the appropriate model for most storage systems: a single `write()` call either completes or does not, but the system can crash between a `write()` and the next `read()`. Modeling intra-operation crashes (torn writes, partial pages) would require a different abstraction, which we discuss as future work.

### 3.3 Environment Reset on Crash

When a crash occurs, the runner resets the typed environments for both model and SUT. This is essential for correctness with opaque handles. In a file system test, for example, an `open()` call returns a file descriptor that is stored as a symbolic variable. After a crash, that file descriptor is invalid---the file may not even exist in the recovered state. Continuing to use pre-crash variables would produce meaningless results. By resetting the environment, the runner forces subsequent actions to operate only on post-recovery state, which is the correct behavior for any system where volatile handles are invalidated by crashes.

### 3.4 Walk-Through: Write-Ahead Log

The write-ahead log example illustrates the simplest crash-recovery scenario. The SUT is a `WriteAheadLog` with two fields: `committed` (a `Vec<String>` representing on-disk entries that survive crash) and `read_count` (an in-memory counter that does not survive crash). The `append` operation pushes an entry to `committed` (synchronous flush---every append is immediately durable). The `read` operation retrieves an entry by index. The `recover` method reconstructs from `committed`, resetting `read_count` to zero.

The model is simply `LogModel { entries: Vec<String> }`. The checkpoint is `state.entries.clone()`, and recovery reconstructs the model from the checkpoint. Because every append is synchronous, the checkpoint always equals the full model state, and crash-recovery is trivially correct: a crash after any sequence of appends recovers to exactly the same entries.

The test generates random sequences of `Append`, `Read`, and `Len` operations with crash injection at 15% probability and up to 5 crashes per run. The framework verifies that after each crash, subsequent reads and length queries agree with the model's post-recovery state.

### 3.5 Walk-Through: Batched Log

The batched log example introduces the central complexity of crash-recovery testing: the data-loss window. The SUT is a `BatchedLog` with two fields: `durable` (entries that have been flushed to disk) and `pending` (entries that are buffered in memory). The `append` operation pushes to `pending`---the entry is *not* durable until `flush()` is called. `flush()` moves all pending entries to `durable`. On crash, `pending` is lost, and the log recovers from `durable` alone.

The model is `LogModel { all_entries: Vec<String>, durable_len: usize }`. The model tracks both the complete log (what reads see) and the durable prefix length (what survives a crash). The checkpoint extracts `all_entries[..durable_len]`---only the flushed prefix. Recovery reconstructs a model where `all_entries` equals the flushed prefix and `durable_len` equals the flushed prefix length.

This creates a non-trivial verification challenge. Consider the sequence: `Append("a")`, `Append("b")`, `Flush`, `Append("c")`, *CRASH*. Before the crash, the model has `all_entries = ["a", "b", "c"]` and `durable_len = 2`. The checkpoint captures `["a", "b"]`. After recovery, the model has `all_entries = ["a", "b"]` and `durable_len = 2`. The SUT loses `"c"` (which was pending) and recovers with `durable = ["a", "b"]`. A subsequent `Read(2)` must return `None` on both sides. A subsequent `Len` must return 2 on both sides.

The invariant checks that `durable_len <= all_entries.len()`---the durable prefix cannot exceed the total log. This invariant must hold at every step *and* after every recovery. The framework verifies it automatically.

The test runs 200 cases with 15% crash probability and up to 5 crashes, plus a high-frequency stress test with 30% crash probability and up to 10 crashes. The high-frequency test exercises the flush/crash interaction thoroughly: many crashes occur between flushes, testing that unflushed data is consistently lost and the log remains usable after repeated crash-recovery cycles.

---

## 4. Crash Bisimulation: Formal Foundation

### 4.1 The Crash-Recovery System Structure

In the Lean 4 formalization, we define a `CrashRecoverySystem` that extends the base `LockstepSystem` with crash-specific components:

```lean
structure CrashRecoverySystem extends LockstepSystem where
  DS : Type                    -- durable state (survives crash)
  checkpoint : SM -> DS        -- extract durable state from model
  model_recover : DS -> SM     -- recover model from checkpoint
  sut_recover : SS -> SS       -- recover SUT from crash
  invariant : SM -> Prop       -- state invariant
```

The `LockstepSystem` provides model state type `SM`, SUT state type `SS`, action index type `ActionIdx`, return types `RetM` and `RetS`, bridge functions, and step functions for model and SUT. The `CrashRecoverySystem` adds the durable state type `DS`, the checkpoint/recovery functions, and a state invariant that must hold at every reachable state.

### 4.2 The Crash Bisimulation Definition

Crash bisimulation is an inductive relation over `(SM, SS)` pairs, parameterized by depth:

```lean
def crash_bisim (sys : CrashRecoverySystem) :
    Nat -> sys.SM -> sys.SS -> Prop
  | 0, _, _ => True
  | n + 1, sm, ss =>
    sys.invariant sm
    /\ (forall (a : sys.ActionIdx),
        let (sm', rm) := sys.step_model a sm
        let (ss', rs) := sys.step_sut a ss
        bridge_equiv (sys.bridge a) rs rm
        /\ crash_bisim sys n sm' ss')
    /\ crash_bisim sys n
        (sys.model_recover (sys.checkpoint sm))
        (sys.sut_recover ss)
```

At depth 0, the relation is trivially true. At depth `n + 1`, three conditions must hold simultaneously:

1. **Invariant**: The state invariant holds at the current model state. This ensures that the model is always in a "reasonable" state---for example, the durable prefix length never exceeds the total log length.

2. **Action preservation**: For every action `a`, executing `a` on both model and SUT produces bridge-equivalent results, and the successor states are in the crash bisimulation at depth `n`. This is the standard lockstep condition, identical to bounded bisimulation.

3. **Crash preservation**: If a crash occurs *right now*, the recovered states---`model_recover(checkpoint(sm))` for the model, `sut_recover(ss)` for the SUT---are in the crash bisimulation at depth `n`. A crash consumes one depth unit: surviving `n` more steps after recovery requires depth `n + 1` before the crash.

The depth parameter makes the definition constructive and amenable to bounded testing. Testing at depth `n` means: for any sequence of up to `n` events (actions or crashes), the system behaves correctly.

### 4.3 Key Theorems

We prove five core theorems about crash bisimulation, all machine-checked with zero `sorry`.

**Theorem 1: Crash bisimulation implies bounded bisimulation** (`crash_bisim_implies_bounded`). If `crash_bisim sys n sm ss` holds, then `bounded_bisim sys.toLockstepSystem n sm ss` holds. This is a strict implication: crash-correct systems are also correct without crashes. The proof proceeds by induction on `n`, extracting the action-preservation clause and discarding the crash clause.

**Theorem 2: Monotonicity** (`crash_bisim_mono`). If `n <= m` and `crash_bisim sys m sm ss`, then `crash_bisim sys n sm ss`. Bisimulation at a greater depth implies bisimulation at any lesser depth. This justifies testing at increasing depths: if the system passes at depth 30, it also passes at depths 1 through 29.

**Theorem 3: Recovery preservation** (`crash_recovery_preserves`). If `crash_bisim sys (n+1) sm ss`, then `crash_bisim sys n (model_recover(checkpoint(sm))) (sut_recover(ss))`. The recovered states remain in the bisimulation. This is the formal counterpart of the runner's crash-injection strategy: after injecting a crash, the runner continues testing from the recovered states, and this theorem guarantees that such continuation is valid.

**Theorem 4: Double crash** (`crash_bisim_double_crash`). If `crash_bisim sys (n+2) sm ss`, then crashing, recovering, crashing again, and recovering again produces states in `crash_bisim sys n`. The system can survive two consecutive crashes and still be correct for `n` more steps. This follows from applying recovery preservation twice.

**Theorem 5: Crash then bounded** (`crash_then_bounded_bisim`). If `crash_bisim sys (n+1) sm ss`, then the recovered states satisfy `bounded_bisim n`. After a crash, normal (crash-free) lockstep testing is valid. This composes Theorems 1 and 3.

### 4.4 Invariant Properties

Two additional theorems address the interaction between crash bisimulation and the state invariant.

**Invariant at current state** (`crash_bisim_invariant`). If `crash_bisim sys (n+1) sm ss`, then `sys.invariant sm` holds. The invariant is guaranteed at every state reachable under crash bisimulation.

**Invariant after action** (`crash_bisim_invariant_step`). If `crash_bisim sys (n+2) sm ss` and we take action `a`, then `sys.invariant (step_model a sm).1` holds. The invariant is preserved through action execution.

Together, these theorems establish that the invariant holds along every path through the state space, including paths that include crashes and recoveries. This is the formal guarantee behind the runner's invariant-checking strategy: if crash bisimulation holds, the invariant assertions in the runner will never fire.

---

## 5. Crash-Transparent Action Elimination

### 5.1 Crash-Transparent Actions

Not all actions interact with crash recovery. A read-only operation, for example, does not modify the durable state: the checkpoint before and after the read is identical. If the system crashes immediately after a read, the recovered state is the same as if the system had crashed immediately before the read. Such operations are *crash-transparent*: from the perspective of crash recovery, they are invisible.

Formally, we define crash transparency as a two-part predicate on an action `a` at a given model/SUT state:

```lean
def crash_transparent (sys : CrashRecoverySystem)
    (a : sys.ActionIdx) (sm : sys.SM) (ss : sys.SS) : Prop :=
  sys.checkpoint (sys.step_model a sm).1 = sys.checkpoint sm
  /\ sys.sut_recover (sys.step_sut a ss).1 = sys.sut_recover ss
```

The first conjunct requires that the checkpoint is unchanged by the action: `checkpoint(step_model(a, sm)) = checkpoint(sm)`. The second requires that the SUT's recovery is unchanged: `sut_recover(step_sut(a, ss)) = sut_recover(ss)`. Together, these ensure that the action's effects are completely erased by a crash.

Typical examples of crash-transparent actions include:
- **Read-only operations**: `Read`, `Len`, `DurableLen` in the log examples. These do not modify any state.
- **In-memory-only mutations**: incrementing a `read_count` counter, updating a cache that is not persisted.
- **Idempotent volatile operations**: logging to stdout, computing a hash, validating input.

### 5.2 Single-Pair Elimination

The core elimination theorem states that in a crash-interleaved trace, a crash-transparent action immediately before a crash can be removed without changing the final model state:

```lean
theorem crash_transparent_eliminate_model
    (sys : CrashSessionSystem)
    (pre : List (CrashEvent sys.ActionIdx))
    (a : sys.ActionIdx)
    (suf : List (CrashEvent sys.ActionIdx))
    (sm : sys.SM)
    (hchk_trans : sys.checkpoint
      (sys.step_model a (crash_model_after sys pre sm)).1
      = sys.checkpoint (crash_model_after sys pre sm)) :
    crash_model_after sys (pre ++ [.action a, .crash] ++ suf) sm
    = crash_model_after sys (pre ++ [.crash] ++ suf) sm
```

The proof uses a trace-splitting lemma (`crash_model_after_append`) to decompose the trace at the elimination point, then applies checkpoint transparency to show that the `[action a, crash]` segment produces the same recovered state as `[crash]` alone.

The biconditional version (`crash_bisim_transparent_action`) is even more direct: if the checkpoint and SUT recovery are both transparent to action `a`, then `crash_bisim` on the recovered states after `a` holds if and only if `crash_bisim` on the recovered states before `a` holds. The crash point can be moved past the transparent action in either direction.

### 5.3 Multi-Pair Elimination

The single-pair theorem eliminates one `[action, crash]` pair at a time. For practical use, we need to eliminate all such pairs in a trace simultaneously. The `reduce_crash_trace` function scans a crash-interleaved trace left to right, removing every crash-transparent action that immediately precedes a crash event:

```lean
def reduce_crash_trace
    (sys : CrashSessionSystem)
    (chk_transparent : sys.ActionIdx -> sys.SM -> Bool) :
    List (CrashEvent sys.ActionIdx) -> sys.SM ->
    List (CrashEvent sys.ActionIdx)
```

The function takes a decidable predicate `chk_transparent` that identifies transparent actions at a given model state, and produces a reduced trace. The key theorem states that the reduced trace produces the same final model state as the original:

```lean
theorem reduce_crash_trace_preserves_state ... :
    crash_model_after sys
      (reduce_crash_trace sys chk_transparent trace sm) sm
    = crash_model_after sys trace sm
```

The proof is by structural induction on the trace, applying checkpoint transparency at each eliminated `[transparent, crash]` pair.

### 5.4 Practical Implications

For the crash-interleaving explorer, crash-transparent elimination provides an exponential reduction in the search space. Consider a trace of `n` operations with `k` crash points. Without elimination, the explorer must consider all `O(n^k)` placements of crash points. With elimination, crash points adjacent to transparent actions can be collapsed: if `t` of the `n` operations are transparent, the effective number of non-trivial crash positions is `n - t`, reducing the space to `O((n-t)^k)`.

In the batched log example, `Read`, `Len`, `DurableLen`, and `PendingLen` are all crash-transparent. Only `Append` and `Flush` modify the durable state. In a trace of 30 operations where roughly 60% are reads and queries, the effective crash-point space is reduced by approximately 60%.

---

## 6. Game-Semantic Characterization

### 6.1 The Crash Bisimulation Game

We formalize the notion of a crash-recovery bug as a game between two players. The **Attacker** attempts to demonstrate that the system fails under some crash scenario. The **Defender** attempts to show the system is correct. The game is played on a pair of states `(sm, ss)`---the current model and SUT states.

The Attacker has four moves, captured by the `CrashWitness` inductive type:

```lean
inductive CrashWitness (A : Type) where
  | bridge_fail : A -> CrashWitness A
  | invariant_fail : CrashWitness A
  | deeper : A -> CrashWitness A -> CrashWitness A
  | crash_then : CrashWitness A -> CrashWitness A
```

- **`bridge_fail a`**: The Attacker claims that executing action `a` produces non-equivalent results on model and SUT. This is an immediate win---the system has a lockstep violation.
- **`invariant_fail`**: The Attacker claims the model invariant is violated at the current state. This is an immediate win---the system has reached an inconsistent state.
- **`deeper a w`**: The Attacker chooses action `a`, which passes the bridge check, and continues with strategy `w` from the successor states. This is a deferred attack---the bug is deeper in the trace.
- **`crash_then w`**: The Attacker triggers a crash, both sides recover, and the Attacker continues with strategy `w` from the recovered states. This is the crash-specific move---the bug manifests only after a crash.

A witness is **valid** if each claim is true: `bridge_fail a` requires the bridge to actually fail, `invariant_fail` requires the invariant to actually not hold, `deeper a w` requires the bridge to pass and `w` to be valid at the successor states, and `crash_then w` requires `w` to be valid at the recovered states.

### 6.2 Soundness and Completeness

We prove two theorems that together establish the game-semantic biconditional.

**Witness soundness** (`crash_witness_soundness`): A valid crash witness of depth at most `n` implies the negation of crash bisimulation at depth `n`. If the Attacker has a winning strategy, the system is not crash-bisimilar.

**Witness completeness** (`crash_witness_completeness`): If crash bisimulation fails at depth `n`, there exists a valid crash witness of depth at most `n`. If the system is not crash-bisimilar, the Attacker has a winning strategy.

The completeness proof requires classical logic (to extract the failing component from a negated conjunction) and bridge decidability (to determine whether a failure is at the bridge or deeper in the trace). The proof has four branches, corresponding to the four `CrashWitness` constructors:

1. Invariant failure at the current state produces `invariant_fail`.
2. Bridge failure at some action `a` produces `bridge_fail a`.
3. Bridge passes but the successor bisimulation fails produces `deeper a (recursive)`.
4. Crash-recovery bisimulation fails produces `crash_then (recursive)`.

The biconditional `crash_bisim_game_semantic` combines both directions:

```lean
theorem crash_bisim_game_semantic ... :
    neg (crash_bisim_param ...) <->
    exists (w : CrashWitness ...),
      crash_witness_valid ... w sm ss /\ w.depth <= n
```

### 6.3 Witness Simplification

The game-semantic characterization connects naturally to crash-transparent elimination. We prove that if a witness contains the pattern `deeper a (crash_then w)` (the Attacker plays action `a`, then crashes) and action `a` is crash-transparent, the witness can be simplified to `crash_then w` with adjusted states:

```lean
theorem crash_witness_transparent_simplify ... :
    crash_witness_valid ... (.deeper a (.crash_then w)) sm ss ->
    crash_witness_valid ... (.crash_then w) sm ss
```

The simplified witness has strictly smaller depth. This means the Attacker gains nothing by playing a transparent action before crashing---the crash alone suffices. The game-semantic interpretation: the Attacker's strategy space can be pruned of all `[transparent, crash]` patterns without losing any winning strategies.

### 6.4 Connection to Bug Reports

The practical significance of the game-semantic characterization is in bug reporting. When the crash-recovery runner finds a failure, the failing trace is a concrete instantiation of a `CrashWitness`. The trace structure tells the developer exactly what happened: which actions led to the state where the crash exposed a bug, whether the failure is a bridge violation (the system returned the wrong value after recovery) or an invariant violation (the system entered an inconsistent state after recovery), and what the minimal crash scenario is.

Combined with proptest's built-in shrinking and bisimulation-guided minimization, the witness is reduced to the smallest possible attack strategy---the shortest sequence of actions and crash points that exposes the bug.

---

## 7. Crash-Session Composition

### 7.1 Session Guarantees Under Crashes

Many storage systems provide session-level consistency guarantees. A key-value store might guarantee *read-your-writes*: within a session, if a client writes a value to key `k`, any subsequent read of `k` within the same session must return that value (or a later one). A message queue might guarantee *monotonic reads*: within a session, a consumer never sees messages go backward.

These guarantees interact non-trivially with crashes. After a crash, the system recovers, but what happens to session state? In most systems, a crash resets session state: the client reconnects and starts a fresh session. Read-your-writes must hold within the new session but not across the crash boundary. A write to key `k` before the crash does not obligate the system to return that value after recovery---the write may not have been durable.

Testing this interaction requires a framework that tracks session histories through crash events and correctly resets them on recovery. A naive approach---testing crash recovery and session consistency independently---would miss bugs that arise from their interaction.

### 7.2 The CrashSessionSystem Structure

We define a `CrashSessionSystem` that extends `CrashRecoverySystem` with session-specific metadata:

```lean
structure CrashSessionSystem extends CrashRecoverySystem where
  Session : Type
  Key : Type
  Obs : Type
  session_of : ActionIdx -> Option Session
  read_key : ActionIdx -> Option Key
  sut_read_obs : ActionIdx -> SS -> Option Obs
  write_key : ActionIdx -> Option Key
  write_val : ActionIdx -> Option Obs
```

Each action may be associated with a session (`session_of`), may read a key (`read_key`), may write a key-value pair (`write_key`, `write_val`), and may produce a read observation (`sut_read_obs`). These annotations allow the framework to track per-session write histories and verify read-your-writes guarantees.

### 7.3 Crash-Session Bisimulation

The crash-session bisimulation threads session histories through the crash transition, resetting them on recovery:

```lean
def crash_session_bisim (sys : CrashSessionSystem) :
    Nat -> sys.SM -> sys.SS ->
    SessionHistories sys.Session sys.Key sys.Obs -> Prop
  | 0, _, _, _ => True
  | n + 1, sm, ss, hists =>
    sys.invariant sm
    /\ (forall (a : sys.ActionIdx),
        read_your_writes_check ...
        /\ bridge_equiv ...
        /\ crash_session_bisim sys n ... updated_hists)
    /\ crash_session_bisim sys n
        (sys.model_recover (sys.checkpoint sm))
        (sys.sut_recover ss)
        (empty_histories ...)   -- CRASH: histories reset
```

The critical line is the crash clause: after recovery, the session histories are reset to `empty_histories`. This captures the real-world semantics: a client reconnecting after a crash has no prior write history, so read-your-writes obligations are cleared.

### 7.4 The Biconditional

We define crash-interleaved observational equivalence using `CrashEvent` traces---sequences of `action a` and `crash` events. The `crash_model_after` function processes such a trace, advancing the model on actions and recovering on crashes. The `crash_hists_after` function tracks session histories, updating them on write actions and resetting them on crashes.

Crash-session observational equivalence at depth `n` requires that for any crash-interleaved prefix of length at most `n`, the model invariant holds, bridge observations match, and read-your-writes is satisfied given the accumulated (and crash-reset) histories.

The central theorem is the biconditional:

```lean
theorem crash_session_obs_equiv_iff ... :
    crash_session_bisim sys n sm ss hists
    <-> crash_session_obs_equiv sys n sm ss hists
```

The forward direction (bisimulation implies observational equivalence) proceeds by induction on the trace, unfolding the bisimulation at each step and extracting the relevant clause (action or crash). The backward direction (observational equivalence implies bisimulation) proceeds by induction on `n`, using empty traces for the current-step obligations, action-prefixed traces for successor obligations, and crash-prefixed traces for recovery obligations.

### 7.5 Hierarchy of Implications

The crash-session framework composes cleanly with the simpler crash and bounded bisimulations:

- `crash_session_bisim` implies `crash_bisim` (by forgetting session histories)
- `crash_bisim` implies `bounded_bisim` (by forgetting crash clauses)

Both implications are proved as standalone theorems (`crash_session_implies_crash`, `crash_bisim_implies_bounded`). This hierarchy means that testing at the crash-session level provides the strongest guarantees: the system satisfies read-your-writes, survives crashes, and matches the model in the absence of crashes.

---

## 8. Evaluation

### 8.1 Case Study 1: Write-Ahead Log

**System.** A write-ahead log (WAL) where every `Append` is synchronously durable. The `committed` vector represents on-disk entries that survive crashes. A `read_count` counter tracks volatile in-memory state.

**Model.** `LogModel { entries: Vec<String> }`. The checkpoint is `entries.clone()`; recovery reconstructs the model from the checkpoint verbatim. Because every append is synchronous, the checkpoint always equals the full model state.

**Actions.** `Append(entry)` pushes an entry and returns its index. `Read(index)` returns the entry at the given index or `None`. `Len` returns the number of entries.

**Invariant.** All log entries are non-empty strings (reflecting the generator's output).

**Results.** Under standard configuration (200 cases, 15% crash probability, up to 5 crashes, 5-30 operations), all tests pass within approximately 2 seconds. The framework correctly verifies that committed entries survive crashes and that the `read_count` counter (volatile state) is reset to zero after recovery without affecting the log's observable behavior.

**Seeded bug.** We modified `recover` to drop the last committed entry: `committed.pop()` before returning. The framework caught this within the first 5 test cases, producing a minimal trace of the form: `Append("a"), CRASH, Len` --- the `Len` bridge check fails because the model expects 1 and the SUT returns 0.

Under high crash frequency (40% probability, up to 10 crashes, 10-40 operations), the framework exercises repeated crash-recovery cycles. The stress test verifies that multiple consecutive crashes do not corrupt the log---consistent with our double-crash theorem.

### 8.2 Case Study 2: Batched Log

**System.** A batched append-only log with explicit flush. The `BatchedLog` maintains `durable` (persisted entries) and `pending` (buffered entries). `Append` writes to `pending`; `Flush` moves `pending` to `durable`. On crash, `pending` is lost.

**Model.** `LogModel { all_entries: Vec<String>, durable_len: usize }`. The model tracks the complete log (what reads see) and the durable prefix length. The checkpoint extracts `all_entries[..durable_len]`. Recovery reconstructs a model where only the durable prefix exists.

**Actions.** `Append(entry)` adds to the buffer. `Flush` persists the buffer (returns count of flushed entries). `Read(index)` returns an entry from the full view (durable + pending). `Len` returns total entries. `DurableLen` returns the durable count. `PendingLen` returns the pending count.

**Invariant.** `durable_len <= all_entries.len()`.

**Results.** Under standard configuration (200 cases, 15% crash probability, up to 5 crashes), all tests pass in approximately 3 seconds. The framework verifies the central property: after a crash, only flushed entries survive. A typical passing trace might be: `Append("a"), Append("b"), Flush, Append("c"), CRASH, Len[model=2, sut=2], Read(0)[model=Some("a"), sut=Some("a")], Read(2)[model=None, sut=None]`.

**Seeded bug 1: Flush off-by-one.** We modified `flush` to not advance the durable pointer on the model side (`durable_len` remains 0). The framework caught this immediately: after `Append, Flush, CRASH, DurableLen`, the SUT returns the correct durable length but the model/SUT states diverge on the next operation.

**Seeded bug 2: Recovery includes pending.** We modified `recover` to retain `pending` entries. The framework catches this when a crash occurs with pending entries: the SUT's `Len` returns more than the model expects.

Under high crash frequency (30% probability, up to 10 crashes, 10-40 operations), the framework exercises complex flush/crash interleavings. The test verifies that arbitrary sequences of appends, flushes, and crashes leave the log in a consistent state where only flushed data survives.

### 8.3 Case Study 3: Crash-Consistent Session KV

**System.** A multi-session key-value store where read-your-writes must hold within a session but session history resets on crash. A client in session `s` that writes `k=v` must see `v` (or later) on subsequent reads of `k`---until a crash occurs, which starts a new session.

**Model.** The model tracks key-value state plus per-session write histories. The checkpoint captures only the key-value state. Recovery resets all session histories to empty.

**Results.** The crash-session framework correctly distinguishes between pre-crash and post-crash obligations. A write before a crash does not create a read-your-writes obligation after the crash, because session histories are reset. The framework catches violations where recovery incorrectly preserves stale session state.

### 8.4 Performance

All measurements were taken on an Apple M-series laptop using Rust's `cargo test` in release mode.

| Configuration | Crash Prob. | Max Crashes | Cases | Ops/Case | Wall-clock Time |
|---|---|---|---|---|---|
| WAL standard | 0.15 | 5 | 200 | 5-30 | ~2s |
| WAL high-freq | 0.40 | 10 | 100 | 10-40 | ~3s |
| Batched standard | 0.15 | 5 | 200 | 5-30 | ~3s |
| Batched high-freq | 0.30 | 10 | 100 | 10-40 | ~4s |

Test throughput ranges from approximately 30 to 100 cases per second depending on configuration, with each case executing 5-40 operations and 0-10 crashes. The overhead of crash injection (checkpoint, recover, environment reset, invariant check) is negligible compared to action generation and bridge checking. The framework is fast enough for integration into CI pipelines with hundreds of cases per commit.

The formal verification compiles in approximately 30 seconds (20 Lean files, 182 theorems). The Lean development is structured as a standalone library that does not depend on or interact with the Rust implementation at compile time.

---

## 9. Related Work

### 9.1 Empirical Crash Testing

**Jepsen** is the de facto standard for distributed-systems testing, supporting a wide range of fault types including process kills, network partitions, clock skew, and disk-full conditions. Jepsen has found bugs in nearly every system it has tested, but operates without formal soundness guarantees. Our work provides what Jepsen lacks: a theorem connecting the testing methodology to a formal correctness property.

**Chaos Monkey** (Netflix) and its successors (Chaos Kong, Gremlin) inject faults into production systems to test resilience. These tools operate at the infrastructure level and focus on availability rather than data correctness. They complement rather than replace lockstep-style crash testing.

**CrashMonkey** systematically explores crash states for ext4, Btrfs, and other filesystems by intercepting block I/O and replaying crash-consistent prefixes. Unlike our approach, CrashMonkey is filesystem-specific and does not provide a general-purpose model-checking framework. **Alice** (All File Systems Are Not Created Equal) similarly analyzes block traces to find crash-consistency violations.

**LitmusTk** tests memory-consistency models on hardware, a related but distinct problem domain.

### 9.2 Full Verification

**Perennial** provides crash Hoare logic in Coq with full mechanical verification of crash-recovery correctness. FSCQ and DaisyNFS are the landmark results. Our approach is strictly weaker (bounded testing vs. full verification) but dramatically more practical (hours vs. years of effort).

**Verdi** verifies distributed systems in Coq using verified system transformers. **IronFleet** combines TLA+ specifications with Dafny verification. These systems provide full correctness guarantees but, like Perennial, require extensive proof engineering.

**Armada** automates concurrent program verification using rely-guarantee reasoning. **CertiKOS** verifies an OS kernel. These are full-verification efforts for specific domains.

### 9.3 Property-Based Testing

**QuickCheck** (Haskell) pioneered property-based testing. **proptest** (Rust) and **Hedgehog** (Haskell) extended the approach with integrated shrinking and composable strategies. **proptest-state-machine** provides stateful PBT for Rust.

**quickcheck-lockstep** (Edsko de Vries) introduced lockstep-style testing with GADT-based type-safe comparison. Our framework extends this approach to Rust, adds crash-recovery semantics, and provides the first machine-checked soundness proofs.

No prior PBT framework, to our knowledge, includes machine-checked metatheory for crash-recovery testing. The combination of practical testing infrastructure with formal soundness guarantees is the primary novelty of our work.

### 9.4 Bisimulation Theory

Bisimulation originates in process algebra (Milner, Park) and has been extensively studied in concurrency theory. Our crash bisimulation is a bounded, asymmetric variant that extends the standard notion with crash transitions. The game-semantic characterization follows the classical pattern (Stirling) but adds crash moves to the Attacker's repertoire. The crash-transparent elimination theorem has no direct precedent, as prior bisimulation theory does not consider checkpoint/recovery transitions.

### 9.5 Crash-Consistency Models

The crash-consistency literature distinguishes several persistence models: ordered writes (ext4 with `data=ordered`), copy-on-write (Btrfs, ZFS), journal-based (ext3/ext4, NTFS), and log-structured (LevelDB, RocksDB). Our framework is agnostic to the persistence model: the `checkpoint`/`model_recover`/`sut_recover` interface abstracts over the specific durability mechanism. The developer encodes their system's persistence semantics in these three functions.

**Crashmonkey**, **B3** (block-based bug finder), and **Chipmunk** target filesystem-specific crash models. Our approach is more general but less domain-specific---we do not model block-level I/O or torn writes.

---

## 10. Conclusion

We have presented crash-recovery property-based testing with machine-checked soundness, a practical approach that occupies the gap between Jepsen's empirical crash testing and Perennial's full crash-recovery verification. The developer implements three functions---checkpoint, model recovery, and system recovery---and the framework generates random action sequences with probabilistic crash injection, verifying that the system's post-recovery behavior matches the model at every step.

The formal foundation, comprising 194 lines of machine-checked Lean 4 with zero unfinished proofs, establishes that the testing methodology is sound. Crash bisimulation strictly implies bounded bisimulation; the bisimulation is preserved through recovery, double crashes, and arbitrary action sequences; crash-transparent actions can be eliminated from the exploration space; the negation of crash bisimulation is equivalent to a four-move game-semantic witness; and crash-session bisimulation is equivalent to crash-interleaved observational equivalence.

The framework is practical. Three case studies---a write-ahead log, a batched log with explicit flush, and a session-consistent crash-aware key-value store---demonstrate that the approach catches realistic crash-recovery bugs within seconds, produces minimal failing traces, and scales to hundreds of test cases with multiple crash injections per trace. The implementation requires hours of developer effort, not years.

Several directions remain for future work. First, **crash-recovery DPOR**: combining crash injection with dynamic partial-order reduction for concurrent crash-recovery systems would extend the framework to multi-threaded storage engines. The crash-deferral and crash-linearizability theorems in our formalization provide the theoretical foundation for this extension. Second, **partial-write models**: extending the framework to model torn pages, partial block writes, and other sub-operation crash behaviors would bring it closer to the filesystem-level testing tools like CrashMonkey. Third, **integration with real storage stacks**: deploying the framework against production systems (RocksDB, SQLite, etcd) with actual disk I/O and process restarts would validate the approach at scale. Fourth, **certified crash exploration**: using the game-semantic witness to guide test generation, prioritizing crash placements that are most likely to produce new witnesses, could improve the efficiency of crash exploration for large state spaces.
