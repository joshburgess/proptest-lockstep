# lambda-bridge Round 5: Final Assessment

## Status: Fully Subsumed

The lambda-bridge calculus is now completely subsumed by the Lean formalization. Every construct in the calculus has a machine-checked counterpart:

| Calculus Element | Lean File | Status |
|-----------------|-----------|--------|
| Bridge formation | Bridge.lean | ✅ 23 theorems |
| Observation typing | Bridge.lean (decidability) | ✅ |
| Projection typing | Projection.lean | ✅ 27 theorems |
| Phase distinction | (not needed — Lean uses dependent types) | ✅ |
| Runner judgment | Runner.lean + Environment.lean | ✅ biconditional |
| Bisimulation | Lockstep.lean | ✅ 7 theorems |
| DPOR | DPOR.lean | ✅ 9 theorems |
| Crash modality | CrashRecovery.lean | ✅ 9 theorems |
| Compositional products | Compositional.lean | ✅ 7 theorems |
| Tensor products | TensorProduct.lean | ✅ 5 theorems |
| Effect annotations | EffectLattice.lean | ✅ 8 theorems |
| Certified synthesis | CertifiedSynthesis.lean + CertificateHash.lean | ✅ 38 theorems |
| Derivation correctness | DeriveBridge.lean | ✅ 8 theorems |

**Recommendation:** Reference the Lean formalization directly in papers. The calculus served its purpose as a design document and can be cited as historical context.
