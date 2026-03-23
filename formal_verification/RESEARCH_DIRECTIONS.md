# Research Directions for proptest-lockstep

Ideas enabled by the complete 305-definition formal verification infrastructure (29 Lean files, zero sorry, 12 rounds of adversarial review). These build on the new definitions added in Rounds 9-10: `swap_reachable`, `sleep_set_equiv`, `session_bisim_full`, `crash_session_bisim` (with history reset), and `product_refines_bisim`.

## 1. Crash-Consistent Linearizability via Sleep Set Quotients

**Pitch:** Combine `sleep_set_equiv` with `crash_session_bisim` to prove that crash-consistent linearizability checking can quotient out both commuting swaps AND crash-equivalent recovery paths, giving an exponential reduction in the exploration space.

**Key insight:** Two equivalence relations on operation sequences now exist in the formalization:
1. `swap_reachable` (DPOR): permutations reachable by commuting swaps are equivalent for `linearization_check`
2. Crash-recovery equivalence: sequences differing only by crash points followed by history-resetting recovery are equivalent for `crash_session_bisim`

These compose: the quotient by both relations is strictly smaller than either alone. A crash during a commuting sequence can be "moved" past the commuting operations (because they don't affect the durable state).

**Target theorem:**
```lean
theorem crash_commute_defer (sys : CrashSessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (r1 r2 : OpRecord sys.toLockstepSystem) (sm : sys.SM)
    (hcomm : model_commute sys.toLockstepSystem r1.action r2.action sm)
    -- crash between r1 and r2 is equivalent to crash after both
    ...
```

**Requires:** Both `swap_reachable` (to move operations) and `crash_session_bisim` (to handle history reset). Neither alone suffices.

**Crux:** Proving checkpoint/model_recover are "transparent" to commuting swaps.

**Effort:** 2-3 weeks. **Venue:** CONCUR/POPL.

## 2. Session-Aware DPOR — Commutativity Modulo Session Isolation

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

**Requires:** `session_bisim_full` with `update_read` threading — proving `update_write`/`update_read` at session s and session s' commute when s != s'.

**Effort:** 1-2 weeks. **Venue:** ICFP/ISSTA.

## 3. Incremental Compositional Refinement

**Pitch:** Use `product_refines_bisim` to prove that testing a composed system allows upgrading bridges one subsystem at a time, reusing previous results for unchanged subsystems.

**Key insight:** `product_refines_bisim` + `compositional_bisim` say: if subsystem A already passes with its current bridges, and subsystem B is re-tested with finer bridges, the product passes without re-testing A.

**Target theorem:**
```lean
theorem incremental_refinement (sys1 sys2 : LockstepSystem)
    (bridge2' : (a : sys2.ActionIdx) → Bridge (sys2.RetS a) (sys2.RetM a))
    (hrefine2 : ∀ a, bridge_refines (sys2.bridge a) (bridge2' a))
    (n : Nat) (sm1 ss1 sm2 ss2)
    (h1 : bounded_bisim sys1 n sm1 ss1)
    (h2' : bounded_bisim { sys2 with bridge := bridge2' } n sm2 ss2) :
    bounded_bisim (product_system sys1 { sys2 with bridge := bridge2' })
        n (sm1, sm2) (ss1, ss2)
```

**Why it matters:** Enables a practical workflow: start with all-opaque bridges (fast), then refine one subsystem at a time. Previous subsystem results are reusable.

**Effort:** 1 week. **Venue:** ESOP/OOPSLA.

## 4. Observational Completeness for Crash-Session Systems

**Pitch:** Extend `observational_refinement_equiv` (the biconditional connecting bounded_bisim to observation equality) to `crash_session_bisim`, proving crash-session bisimulation is equivalent to crash-session observational indistinguishability.

**Key insight:** The existing biconditional says `bounded_bisim ↔ observations equal on all traces`. For crash-session, the analogous statement must quantify over traces that include crash events, and post-recovery observations must use reset histories.

**Target theorem:**
```lean
def crash_session_obs_equiv (sys : CrashSessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (hists : SessionHistories sys.Session sys.Key sys.Obs) : Prop :=
  -- For all traces (with interleaved crashes) of depth ≤ n:
  -- 1. Bridge observations match at normal steps
  -- 2. RYW holds at read steps
  -- 3. After crash, (1) and (2) hold with reset histories

theorem crash_session_obs_equiv_iff :
    crash_session_bisim sys n sm ss hists ↔
    crash_session_obs_equiv sys n sm ss hists
```

**Crux:** Defining crash-interleaved traces requires a new inductive type (action | crash). The proof follows `observational_refinement_equiv` with three-way case analysis.

**Effort:** 3-4 weeks. **Venue:** POPL.

## 5. Polynomial Functors for Bridge Algebra

**Pitch:** Prove the bridge algebra is exactly the category of polynomial functor endomorphisms on `Type -> Type`, making "bridges as logical relations" a theorem rather than a metaphor.

**Key insight:** Bridge constructors form a grammar:
```
Bridge ::= Transparent T    -- identity functor
         | Opaque R M        -- constant functor (Unit)
         | Sum B1 B2         -- coproduct
         | Prod B1 B2        -- product
         | Option B          -- Maybe
         | List B            -- free monoid
```

This is the grammar of polynomial functors (Gambino & Kock, 2013). Each bridge defines a polynomial endofunctor `P_B : Type -> Type` where `P_B(X) = B.Observed`. Bridge refinement = natural transformation between polynomial functors.

**Target formalization:**
```lean
-- Functor from polynomial descriptions to bridges
def poly_to_bridge : PolyDesc → Bridge R M

-- Preserves composition
theorem poly_compose : poly_to_bridge (P ∘ Q) = compose_bridge (poly_to_bridge P) (poly_to_bridge Q)

-- Preserves identity
theorem poly_id : poly_to_bridge Id = transparent T

-- Refinement = natural transformation
theorem refines_is_nat_trans : bridge_refines (poly_to_bridge P) (poly_to_bridge Q) ↔ nat_trans P Q
```

**Why it matters:** Upgrades the ICFP pearl story from "bridges look like logical relations" to "bridges ARE polynomial-functor-indexed logical relations" — a categorical theorem connecting to Spivak's work on interactive systems.

**Effort:** 2-3 weeks (core), longer with Mathlib categories. **Venue:** ICFP Pearl.

## Priority Ranking

| # | Idea | Novelty | Effort | Impact | Best Venue |
|---|------|---------|--------|--------|------------|
| 2 | Session-aware DPOR | Very High | 1-2 wk | Very High | ICFP/ISSTA |
| 5 | Polynomial functors | Very High | 2-3 wk | Very High | ICFP Pearl |
| 1 | Crash-consistent linearizability | High | 2-3 wk | High | CONCUR/POPL |
| 4 | Crash-session observational equiv | High | 3-4 wk | High | POPL |
| 3 | Incremental compositional refinement | Medium | 1 wk | Medium | ESOP/OOPSLA |

**Recommended starting point:** Idea 2 (session-aware DPOR) — most impactful, directly enabled by new infrastructure, produces a concrete testing optimization no other framework has.
