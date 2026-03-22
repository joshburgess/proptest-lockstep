# Research Critic Review — Round 3

## Summary

proptest-lockstep has evolved from a lockstep testing library with formal verification into a **comprehensive formally-verified testing platform** spanning multiple consistency models, crash recovery, compositional reasoning, and runtime monitoring. The system now comprises 25 Rust modules, 27 examples, 20 Lean files with 182 machine-checked theorems (zero `sorry`), testing against 4 real crates from crates.io, with 11 novel extension modules — several of which represent firsts in the intersection of formal verification and property-based testing.

## Strengths

- **[S1] The consistency hierarchy is the standout contribution.** The formally verified chain `linearizability ⟹ session consistency ⟹ eventual consistency`, each with its own bisimulation variant (`bounded_bisim`, `session_bisim`, `convergent_bisim`), is original work. No other testing framework offers multiple formally-verified consistency levels with machine-checked proofs that they form a strict hierarchy. The evmap example — passing EC but failing linearizability on the *same real crate* — is the best demonstration in the entire project.

- **[S2] The breadth of formally-verified extensions is unprecedented.** Crash-recovery bisimulation, commutativity spec soundness, effect lattice soundness, compositional bisimulation, and certified bridge synthesis — each individually would be a solid contribution. Together, they form a *platform* rather than a single tool. No other PBT framework has anything close to this scope of formal backing.

- **[S3] The compositional bisimulation theorem (`product_bisim_iff`) is clean and practically useful.** The biconditional — product bisim holds iff both components hold — enables genuinely modular testing. The proof handles the subtle point that the unchanged subsystem needs monotonicity (`bounded_bisim_mono`) to step down from depth k+1 to k. This is not a trivial observation.

- **[S4] Differential bridge testing is a genuinely novel meta-testing idea.** Testing the test oracles themselves — using bridge refinement to detect when a coarse bridge hides real bugs — has no precedent. The theoretical foundation (`refines_strengthen_bisim`) is clean and the practical implementation is immediately useful.

- **[S5] The bug detection + guided shrinking combination is compelling.** The bug detection example (3 intentional bugs caught) combined with bisimulation-guided shrinking (7 actions → 3 actions for the off-by-one bug) shows the framework finds AND minimizes bugs effectively. The shrinking output (`[step 0] Push(3), [step 1] Push(9), [step 2 — FAILS] Pop`) is exactly what a user needs.

- **[S6] Testing real crates (crossbeam, scc, dashmap, evmap) establishes practical credibility.** The fact that well-tested production crates pass the framework's checks is evidence that it scales. The evmap result (EC passes, linearizability fails) is particularly strong because it validates the consistency hierarchy on real code.

- **[S7] The 182-theorem count is no longer inflated.** After removing thin aliases in Round 2, the remaining theorems are substantive. The new additions (crash bisim, convergent bisim, session bisim, compositional bisim, effect soundness, certified synthesis) all prove non-trivial properties.

## Weaknesses

- **[W1] The project has grown beyond a single paper.** The 25 modules and 11 extensions are too much for any single venue. An ICFP pearl about the bridge algebra would be overwhelmed by crash-recovery, effect lattices, and coverage guidance. An OOPSLA tool paper about the full platform would lack the depth to do justice to the formal verification. The project needs to be *carefully sliced* into multiple focused papers, each with a tight story.

  **Suggested slicing:**
  - **Paper 1 (ICFP Pearl)**: Bridge algebra → logical relation → observational refinement → testing soundness/completeness. ~15 pages, tight narrative.
  - **Paper 2 (OOPSLA/ESOP Tool)**: The full platform — proc macro, DPOR, linearizability, ConflictMaximizing, case studies. ~25 pages, systems focus.
  - **Paper 3 (POPL/ESOP Theory)**: Consistency hierarchy — linearizability → session → eventual, with crash-recovery. ~20 pages, theoretical depth.
  - **Paper 4 (ISSTA/ASE Empirical)**: Case studies on real crates, bug detection, coverage-guided generation, shrinking effectiveness. ~12 pages.

- **[W2] The TypedEnv gap remains.** The most distinctive Rust-side feature (GVar projection chains with opaque handle resolution) is still not formalized in Lean. The formal model uses pure functions `SM → SM × RetM a` without an environment. This means the formal guarantee doesn't cover the most complex usage pattern. At this stage, this is a documentation issue, not a soundness issue — but it should be prominently noted in any paper.

- **[W3] The runtime contracts module (`contracts.rs`) needs more depth.** The `RefinementGuard` is a clean design but the current implementation doesn't address performance overhead (running the model in shadow), state divergence (what happens when the guard and SUT get out of sync after a violation), or partial monitoring (checking only a subset of operations). For a systems venue, these practical concerns matter.

- **[W4] The certified synthesis is more of a marker than a proof-carrying certificate.** The Rust `CertifiedLockstepBridge` trait provides `synthesis_description() -> &'static str` — a documentation string, not a machine-verifiable certificate. The Lean `CertifiedBridge` structure is genuine, but the Rust-Lean connection is informal. A fully integrated system would embed certificate identifiers that can be checked against the Lean proofs. This is aspirational, not a flaw — but the current state should be described honestly.

- **[W5] No end-to-end performance evaluation.** The Criterion benchmarks measure DPOR internals. There are no measurements of: full lockstep test execution time, crash-recovery overhead, eventual consistency sync cost, coverage-guided generation effectiveness vs. random, or shrinking speedup over proptest's default. For any paper targeting a systems or testing venue, these numbers are essential.

## Questions for the Author(s)

- **[Q1]** The compositional bisimulation requires strict independence — actions from sys1 don't affect sys2's state. In practice, how often are real subsystems truly independent? Most layered architectures have shared state (e.g., a database connection pool used by multiple layers). How would you handle shared-nothing vs. shared-something composition?

- **[Q2]** The coverage-guided generation currently tracks buckets but doesn't actively bias generation toward novel buckets — it just records which were visited. The ideation described scoring and biasing. Is active bias planned, or is passive tracking the intended design?

- **[Q3]** The crash-recovery model assumes `sut_recover` is a total function (always succeeds). Real crash recovery can fail (corrupted data, missing WAL entries). How would you model recovery failure?

- **[Q4]** The session consistency checker uses the model to determine whether another session overwrote a value. This requires running the model alongside the SUT at every step — the same overhead as the runtime contracts module. Could session consistency be checked post-hoc from a trace log instead of during execution?

## Minor Issues

- **[M1]** `theory.rs` is becoming unwieldy at 367 lines. Consider splitting into multiple doc modules (one per extension) or generating the documentation from the Lean files.

- **[M2]** Several modules have `#[allow(dead_code)]` warnings that should be cleaned up before publication.

- **[M3]** The `compositional.rs` module's `SubsystemAction` type is defined but not used in the actual runner — the runner takes separate traces, not interleaved actions.

## Overall Assessment

### ICFP Functional Pearl: **Strong Accept** (with slicing)

The bridge algebra → logical relation → observational refinement story is a clear, elegant pearl. The polynomial bridge derivation adds practical value. The formal verification is complete and clean. **But only if the paper focuses solely on this story** — including crash-recovery, effect lattices, etc. would overwhelm the pearl format.

### ESOP/ECOOP Tool Paper: **Strong Accept**

The complete platform — 25 modules, proc macro, DPOR, linearizability, 27 examples — is exceptionally well-engineered. The 4 real-crate case studies add credibility. The formal verification exceeds any comparable tool by an order of magnitude.

### POPL Theory: **Accept** (for the consistency hierarchy)

The formally verified consistency hierarchy (`bounded_bisim ⟹ session_bisim ⟹ convergent_bisim`) with crash-recovery (`crash_bisim`) and compositional bisimulation (`product_bisim_iff`) is a genuine theoretical contribution. The connection to existing work (Herlihy & Wing for linearizability, Terry et al. for session guarantees, Shapiro et al. for CRDTs) is natural.

### OOPSLA: **Accept** (for runtime contracts + differential bridges)

The observational refinement contracts (testing → monitoring) and differential bridge testing (meta-testing of oracles) are novel ideas that bridge the gap between testing and production verification. OOPSLA's audience would appreciate the practical angle.

### ISSTA/ASE: **Accept** (with performance evaluation)

The case studies, bug detection, coverage-guided generation, and guided shrinking are all relevant to a testing venue. **But performance numbers are essential** — how fast is it? How does coverage-guided compare to random? How much does shrinking help?

### OSDI/SOSP: **Weak Accept** (for crash-recovery only)

The crash-recovery extension, with its formal backing and the batched log case study, is relevant but thin for a systems venue. A real-world case study (testing an embedded database like sled) would strengthen it significantly.

## Trajectory: Round 1 → Round 2 → Round 3

| Metric | Round 1 | Round 2 | Round 3 |
|--------|---------|---------|---------|
| Lean theorems | 24 | 119 | 182 |
| Lean files | 3 | 12 | 20 |
| Rust modules | 13 | 13 | 25 |
| Examples | 4 | 13 | 27 |
| Real crates tested | 0 | 0 | 4 |
| Extensions | 0 | 0 | 11 |
| ICFP Pearl verdict | Weak Accept | Accept | **Strong Accept** |
| ESOP/ECOOP verdict | Accept | Strong Accept | **Strong Accept** |
| ISSTA/ASE verdict | Borderline | Weak Accept | **Accept** |
| POPL verdict | — | — | **Accept** |
| OOPSLA verdict | — | — | **Accept** |

**The project has reached maturity.** Further feature development has diminishing returns. The highest-impact next step is **writing papers** — multiple, focused papers targeting different venues with different stories.

## Suggestions for Improvement (ordered by impact)

1. **Write Paper 1 (ICFP Pearl) immediately.** The bridge algebra story is ready. Don't include extensions — they'll be separate papers. Focus: bridge algebra → logical relation → observational refinement → polynomial derivation. Use the file_system and file_system_derived examples for the before/after comparison.

2. **Collect performance numbers.** Before submitting to ISSTA/ASE or any systems venue, measure: (a) full test execution time at various trace lengths, (b) coverage-guided vs. random generation effectiveness, (c) shrinking speedup, (d) crash-recovery overhead. These are essential for credibility.

3. **Write Paper 2 (consistency hierarchy) for POPL.** The `bounded_bisim ⟹ session_bisim ⟹ convergent_bisim` hierarchy with crash-recovery and compositional bisimulation is the strongest theoretical contribution. Use the evmap case study as the motivating example.

4. **Test sled or sqlite for the crash-recovery paper.** The batched log is a good illustration but a real embedded database would be transformative for a systems venue.

5. **Split `theory.rs`.** 367 lines of documentation in a single file is hard to navigate. Consider a `theory/` directory with one file per extension.

6. **Add active bias to coverage-guided generation.** Currently it tracks coverage passively. Active bias (generating candidate actions and selecting the one with the most novel successor state) would make the coverage guidance actually *guide* generation, not just measure it.
