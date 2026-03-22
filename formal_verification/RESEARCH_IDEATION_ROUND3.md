# Research Ideation — Round 3

All previous ideas have been implemented. This round focuses on what the *complete platform* enables that individual features didn't.

## Idea 1: Consistency-Level Inference

**One-sentence pitch:** Automatically determine the strongest consistency level a system satisfies by running it through the hierarchy.

Run linearizability first. If it fails, try session consistency. If that fails, try eventual consistency. Report: "Your system is session-consistent but not linearizable." This is automated consistency classification — no existing tool does this.

**Assessment:** High novelty, high impact, medium difficulty (2-3 weeks). ICFP experience report.

## Idea 2: Cross-Consistency Regression Detection

**One-sentence pitch:** Detect when a code change causes a system to drop from linearizable to merely eventually consistent.

Track the consistency level across versions. If version N is linearizable but version N+1 is only session-consistent, report a regression. This turns the consistency hierarchy into a **regression metric**.

**Assessment:** High novelty, high impact, low difficulty (1-2 weeks). ISSTA paper.

## Idea 3: Tensor Product Composition (Interleaving)

**One-sentence pitch:** Extend compositional bisimulation from independent composition (product) to interleaving composition (tensor product), enabling modular reasoning about shared-state systems.

The current `product_system` requires independence. A tensor product would model shared state: both subsystems can read/write a common resource. The bisimulation would require that shared accesses are properly synchronized.

**Assessment:** Very high novelty, very high difficulty (3-6 months). POPL paper.

## Idea 4: Bridge-Indexed Testing Depth

**One-sentence pitch:** Use the bridge refinement ordering to determine the *minimum testing depth* needed for each action — opaque-bridged actions need deeper testing than transparent ones.

The `opaque_depth_sensitivity` theorem shows that opaque bridges require depth ≥ 2. Generalize: the minimum depth for detecting a wrong opaque handle is 1 + the length of the shortest path from the opaque action to a transparent action that uses the handle.

**Assessment:** High novelty, medium difficulty (2-3 weeks). Extends the pearl story.

## Idea 5: Formal Verification of the Proc Macro

**One-sentence pitch:** Verify that the `derive_bridge` proc macro always produces a bridge matching its `CertifiedBridge` specification, closing the Rust-Lean gap.

Extract the derivation algorithm into a pure function, formalize it in Lean, and prove it correct. The proc macro becomes a "verified compiler" from type descriptions to bridge types.

**Assessment:** Very high novelty, high difficulty (2-3 months). POPL/PLDI paper.

## Priority

1. Consistency-level inference (quick win, high impact)
2. Cross-consistency regression detection (quick win, practical)
3. Bridge-indexed testing depth (extends pearl)
4. Tensor product composition (ambitious theory)
5. Formal verification of the proc macro (ambitious systems)
