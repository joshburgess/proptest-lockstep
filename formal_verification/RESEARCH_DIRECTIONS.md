# Research Directions for proptest-lockstep

Ideas enabled by the complete 305-definition formal verification infrastructure (29 Lean files, zero sorry, 12 rounds of adversarial review). These build on the new definitions added in Rounds 9-10: `swap_reachable`, `sleep_set_equiv`, `session_bisim_full`, `crash_session_bisim` (with history reset), and `product_refines_bisim`.

Effort estimates and venue recommendations reviewed and calibrated by adversarial research critic.

---

## What's Publishable Now (No New Development)

The existing infrastructure supports three papers immediately:

1. **ICFP Functional Pearl**: "Bridges as Logical Relations" — the bridge algebra, polynomial derivation (algorithmic, not categorical), Lean formalization for rigor, Rust examples for impact. 3-4 months writing.

2. **POPL**: "Formal Verification of Lockstep Testing" — comprehensive overview of all 305 definitions, crash-session bisimulation, observational refinement biconditional, consistency hierarchy. Frame as "we machine-checked property-based testing theory." 2 months writing.

3. **OOPSLA Tool Track**: "proptest-lockstep: Practical Stateful PBT for Rust" — the Rust implementation, 29 examples, concurrent testing with DPOR, real crate testing (crossbeam, evmap, dashmap, scc), benchmarks. 1-2 months writing.

---

## Future Research Directions

### 1. Session-Aware DPOR — Commutativity Modulo Session Isolation (Recommended Start)

**Pitch:** Use `session_bisim_full`'s per-session history tracking to prove that operations from different sessions are automatically commuting for session consistency, enabling session-aware DPOR that prunes strictly more than effect-based DPOR.

**Key insight:** `session_bisim_full` checks RYW and monotonic reads per-session. Two operations from different sessions (`session_of(a) != session_of(b)`) cannot violate each other's session guarantees regardless of their effects. This is a new commutativity source orthogonal to `model_commute` and `effect_sound`.

**Target theorem:**
```lean
theorem cross_session_commute (sys : SessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (a b : sys.ActionIdx) (sm : sys.SM) (ss : sys.SS)
    (hists : SessionHistories sys.Session sys.Key sys.Obs)
    (hdiff : sys.session_of a ≠ sys.session_of b) :
    -- History updates for a and b commute (different sessions)
    -- session_bisim_full at [a, b, ...] ↔ session_bisim_full at [b, a, ...]
```

**Why it matters:** Gives proptest-lockstep's concurrent tester a third commutativity source (after `model_commute` and `effect_sound`), specific to session-consistent systems. No existing concurrent testing framework exploits session isolation for DPOR.

**Proof strategy:** Show that `update_write`/`update_read` at session s and session s' commute when s != s' (functional updates on disjoint sessions). Then prove by structural induction on bisimulation depth that the full `session_bisim_full` predicate is preserved under swaps of cross-session actions. Three cases per action type (same session, different session, crash).

**Requires empirical validation:** Once the theorem exists, benchmark the branching factor reduction on concrete session-consistent systems. If the number of cross-session pairs is small, the pruning benefit might be marginal.

**Effort:** 2-3 weeks (formalization) + 1 week (Rust implementation + benchmarks). **Venue:** ICFP/ISSTA.

### 2. Polynomial Functors for Bridge Algebra

**Pitch:** Frame the bridge algebra as polynomial-functor-indexed logical relations, making "bridges as logical relations" precise.

**Key insight:** Bridge constructors (transparent, opaque, sum, prod, option, list) form the grammar of polynomial functors. Each bridge defines a polynomial endofunctor; bridge refinement corresponds to inclusion of logical relations.

**Recommended scope (for ICFP Pearl):** Frame as "bridges are logical relations, and the polynomial structure makes derivation mechanizable." The bridge algebra already forms a lattice with transparent at top and opaque at bottom (`refines_refl`, `refines_trans`, `opaque_coarsest`, `transparent_refines_uniform`). The polynomial derivation is the algorithmic consequence. This is already publication-grade without heavy category theory.

**Extended scope (future work):** The full categorical formalization — bridges as natural transformations between observation functors in a functor category — requires Mathlib's category theory library and 6-10 weeks. Save this for a theory workshop or journal extension, not the pearl submission.

**Crux:** Bridge refinement (`∀ r m, bridge_equiv b1 r m → bridge_equiv b2 r m`) is a logical implication, not a natural transformation. Connecting these requires embedding observation functors into a category where morphisms carry refinement order. This is non-trivial.

**Effort:** 2-3 weeks (pearl-scoped, algorithmic framing). 6-10 weeks (full categorical formalization). **Venue:** ICFP Pearl (rescoped).

### 3. Observational Completeness for Crash-Session Systems

**Pitch:** Extend `observational_refinement_equiv` to `crash_session_bisim`, proving crash-session bisimulation is equivalent to crash-session observational indistinguishability.

**Key insight:** The existing biconditional says `bounded_bisim ↔ observations equal on all traces`. For crash-session, the analogous statement must quantify over traces that include crash events, and post-recovery observations must use reset histories.

**Target formalization:**
```lean
-- Traces with interleaved crash events
inductive CrashAction (A : Type) where
  | action : A → CrashAction A
  | crash : CrashAction A

def crash_session_obs_equiv (sys : CrashSessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (hists : SessionHistories sys.Session sys.Key sys.Obs) : Prop :=
  -- For all crash-interleaved traces of depth ≤ n:
  -- 1. Bridge observations match at normal steps
  -- 2. RYW holds at read steps
  -- 3. After crash, (1) and (2) hold with reset histories

theorem crash_session_obs_equiv_iff :
    crash_session_bisim sys n sm ss hists ↔
    crash_session_obs_equiv sys n sm ss hists
```

**Crux:** Defining the `CrashAction` trace type correctly. The backward direction (observations → bisimulation) requires case analysis on first event (normal action or crash), then structural induction. Test the definition on concrete systems (crash-recovery log, batched log) to verify it captures the right notion before investing in the proof.

**Effort:** 4-5 weeks. **Venue:** POPL.

### 4. Crash-Consistent Linearizability via Sleep Set Quotients

**Pitch:** Combine `sleep_set_equiv` with `crash_session_bisim` to prove that crash-consistent linearizability checking can quotient out both commuting swaps AND crash-equivalent recovery paths.

**Key insight:** Two equivalence relations on operation sequences compose:
1. `swap_reachable` (DPOR): commuting swaps preserve `linearization_check`
2. Crash-recovery equivalence: crash point movement preserves `crash_session_bisim`

The quotient by both is strictly smaller than either alone.

**Target theorem:**
```lean
theorem crash_commute_defer (sys : CrashSessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (r1 r2 : OpRecord sys.toLockstepSystem) (sm : sys.SM)
    (hcomm : model_commute sys.toLockstepSystem r1.action r2.action sm)
    -- crash between r1 and r2 is equivalent to crash after both
    ...
```

**Crux:** Proving `checkpoint` and `model_recover` are "transparent" to commuting swaps — i.e., `model_recover (checkpoint (step r1 (step r2 s))) = model_recover (checkpoint (step r2 (step r1 s)))` when r1 and r2 commute. This is NOT automatic; it requires the checkpoint function to be compatible with commutativity. State this as a precondition.

**Effort:** 2-4 weeks (depends on checkpoint complexity). **Venue:** ISSTA/OOPSLA.

### 5. Incremental Compositional Refinement (Rust Implementation)

**Pitch:** Implement the incremental bridge refinement workflow in Rust: start with all-opaque bridges (fast), then refine one subsystem at a time, reusing previous results.

**Why not formalize:** The target theorem follows in ~5 lines from `product_bisim_iff` + `compositional_bisim` + existing machinery. The formal contribution is trivial. The real value is in the Rust implementation: deciding which bridges to refine, the incremental testing loop, and benchmarks showing practical speedup.

**Implementation plan:**
- Add `IncrementalConfig` to `compositional.rs`
- Track which subsystems have been tested at which bridge precision
- Re-test only subsystems whose bridges changed
- Benchmark on the existing `compositional_test.rs` example

**Effort:** 1-2 weeks (Rust implementation + benchmarks). **Venue:** OOPSLA tool track / Rust conference.

---

## Priority Ranking (Calibrated)

| Priority | Idea | Novelty | Effort | Impact | Best Venue |
|----------|------|---------|--------|--------|------------|
| 1 | Session-aware DPOR | Very High | 2-3 wk | Very High | ICFP/ISSTA |
| 2 | Polynomial functors (rescoped) | Very High | 2-3 wk | Very High | ICFP Pearl |
| 3 | Crash-session obs. equiv | High | 4-5 wk | High | POPL |
| 4 | Crash-consistent linearizability | High | 2-4 wk | High | ISSTA/OOPSLA |
| 5 | Incremental refinement (Rust) | Medium | 1-2 wk | Medium | OOPSLA tool |

**Recommended path:**
1. Start with session-aware DPOR (highest novelty-to-effort ratio)
2. Write the ICFP pearl using the polynomial functor framing (rescoped)
3. If targeting POPL, add crash-session observational completeness
