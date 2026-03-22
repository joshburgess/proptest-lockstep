# Research Ideation — Round 5 (Final)

All previous ideas have been implemented. The project has exhausted the natural feature space. These ideas are for **future work sections in papers**, not immediate implementation.

## Idea 1: Probabilistic Testing Guarantees

**Pitch:** Prove that running N test cases of length L covers a specific fraction of the reachable state space, giving a probabilistic lower bound on bug detection.

**Why it matters:** The one remaining "What Is NOT Formalized" item. Would require probability theory (possibly via Mathlib).

**Venue:** JFP (journal, longer format for the math).

## Idea 2: Incremental Verification

**Pitch:** When the user changes their model, automatically determine which Lean theorems need re-checking and which are unaffected. Like incremental compilation but for formal proofs.

**Why it matters:** Currently, `lake build` re-checks everything. For large formalizations, incremental verification would save time.

**Venue:** PLDI (compilation/tooling focus).

## Idea 3: Bridge Inference from Examples

**Pitch:** Given example input/output pairs from the SUT, infer the correct bridge type automatically — no `real_return` or `opaque_types` annotations needed.

**Why it matters:** Further reduces boilerplate. The current polynomial derivation requires type annotations; bridge inference would work from runtime observations.

**Venue:** OOPSLA (practical tooling).

## Assessment

These are genuinely future work — the current project is complete as-is. Any of these could be a standalone follow-up paper.
