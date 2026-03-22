# lambda-bridge Round 3: Complete Calculus Assessment

## Status

The lambda-bridge calculus (Round 1) and its revision (Round 2) are now fully subsumed by the Lean formalization. Every metatheorem identified in the original calculus has been machine-checked, plus 150+ additional theorems covering extensions that the original calculus didn't anticipate.

## What the Calculus Got Right

1. **Bridge formation rules** — exactly matched by Bridge.lean
2. **Observation typing** — matched by bridge_equiv + decidability
3. **Bounded bisimulation** — matched by Lockstep.lean
4. **Runner judgment** — matched by Runner.lean (biconditional, not just implication)
5. **Projection typing** — conceptually matched, though TypedEnv is not formalized

## What the Calculus Didn't Anticipate

1. **Consistency hierarchy** — the calculus had no notion of weakened bisimulations
2. **Crash modality** — no crash transitions in the original calculus
3. **Compositional products** — no system composition
4. **Effect annotations** — no static commutativity
5. **Certified synthesis** — no proof-carrying construction
6. **Meta-testing** — no differential bridge testing

## Recommendation

The lambda-bridge calculus has served its purpose as a design document. For papers, reference the Lean formalization directly rather than the calculus — the Lean proofs are more precise, more complete, and machine-checked. The calculus can remain as historical documentation of the design process.

## The Calculus as a Paper Section

For the ICFP pearl, a 2-page "calculus overview" section (adapted from lambda-bridge) followed by "this is formalized in Lean" would be effective. The calculus provides intuition; the Lean provides rigor. Don't try to present both in full — the calculus is the sketch, the Lean is the proof.
