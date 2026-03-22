# Research Critic Review — Round 6 (Adversarial)

## Summary

proptest-lockstep: 29 modules, 271 theorems, zero sorry. I was asked to find problems even if the project looks complete. I found several.

## Genuine Weaknesses

### [W1] `session_bisim` doesn't actually check session guarantees.

This is the most serious issue. Look at `SessionConsistency.lean` line 91-100:

```lean
def session_bisim (sys : SessionSystem) :
    Nat → sys.SM → sys.SS → Prop
  | 0, _, _ => True
  | n + 1, sm, ss =>
    ∀ (a : sys.ActionIdx),
      session_bisim sys n (sys.step_model a sm).1 (sys.step_sut a ss).1
```

This definition says: "for each action, the successor states satisfy session_bisim at depth n." But it doesn't use `read_your_writes`, `monotonic_reads`, `SessionHistory`, `session_of`, `read_obs`, `write_obs`, or ANY of the session-specific fields of `SessionSystem`. It's just `bounded_bisim` without the bridge check — structurally identical to "all traces have successors." The `read_your_writes` and `monotonic_reads` definitions exist but are NEVER USED in any theorem.

`bounded_implies_session` is trivially true because `session_bisim` is strictly weaker than `bounded_bisim` (it drops the bridge check and adds nothing). `session_weaker_than_linearizable` is a rename of the same theorem. `ryw_trivial_under_linearizability` is literally `True := trivial`.

**The session consistency formalization proves nothing about session guarantees.** It proves that dropping the bridge check gives a weaker notion — which is trivially true.

**Fix:** `session_bisim` should require that for each action belonging to session `s`, the read observation satisfies `read_your_writes` with respect to that session's history. This requires threading a per-session history through the bisimulation.

### [W2] `monotonic_reads` is trivially true.

```lean
def monotonic_reads (hist : SessionHistory K O) (k : K) (obs : O) : Prop :=
  match hist.last_read k with
  | some v => obs = v ∨ True  -- Simplified: allow any value
  | none => True
```

`obs = v ∨ True` is `True`. This definition accepts ANY observation as monotonic. The comment says "Simplified: allow any value if we can't determine ordering" — but this isn't simplified, it's vacuous.

### [W3] `synthesis_compositional` is `True := trivial`.

```lean
theorem synthesis_compositional : True := trivial
```

The doc comment says "certified constructors preserve bridge_equiv at each level." The theorem proves `True`. A POPL reviewer would call this out immediately. Either prove the actual compositional property or remove the theorem.

### [W4] Several `CertifiedSynthesis` theorems just unfold + call existing theorems.

`certified_sum_ok` unfolds `certify_sum` then calls `sum_preserves_ok`. `certified_prod_sound` unfolds `certify_prod` then calls `prod_preserves`. These aren't wrong, but they're thin wrappers. A hostile reviewer would say: "What does `CertifiedBridge` add over raw `Bridge`? The `CertifiedBridge` structure has one field (`bridge : Bridge R M`) with no proof obligation. The 'certificate' is the fact that you used `certify_sum` instead of `sumBridge` directly — but there's no enforcement. You can construct `{ bridge := sumBridge ... }` without going through `certify_sum`."

**Fix:** Add a proof obligation to `CertifiedBridge`:
```lean
structure CertifiedBridge (R M : Type) where
  bridge : Bridge R M
  sound : ∀ r m, bridge_equiv bridge r m → some_property r m
```

### [W5] The consistency hierarchy `bounded ⟹ session ⟹ convergent` is only implications, not a strict hierarchy.

`bounded_implies_session` and `bounded_implies_convergent` show the implications. But there are no theorems showing the implications are STRICT (i.e., there exist systems where session holds but bounded doesn't). Without strictness, the hierarchy could collapse — all three notions might be equivalent for all you've proved.

**Fix:** Construct a concrete counterexample system for each strict gap:
- A system that satisfies `session_bisim` but not `bounded_bisim`
- A system that satisfies `convergent_bisim` but not `session_bisim`

### [W6] `EnvLockstepSystem` doesn't model type-dependent environments.

The Rust `TypedEnv` stores values of different types keyed by `(usize, TypeId)`. The Lean `EnvLockstepSystem` has `Env : Type` — a single homogeneous type. This means the formalization doesn't capture the key feature of TypedEnv: that variable 0 might store `Result<(Handle, String), Err>` while variable 1 stores `bool`. The `store_model` and `store_sut` functions are opaque, so the formalization doesn't verify that the right types are stored and retrieved.

This was called "closed" in Round 4, but the abstraction is coarser than claimed.

### [W7] `DeriveBridge.lean` uses a simplified derivation that ignores the opaque map.

The `deriveBridge` function:
```lean
| .atom _, .atom _ => .opaque  -- different atoms → opaque
```
All different atoms are opaque — there's no `OpaqueMap` parameter. The actual Rust proc macro checks the `opaque_types` map and errors if a type isn't in it. The formalization just says "different atoms are opaque" without validating the map. `derive_opaque_succeeds` was supposed to use the map but was removed in favor of this simplified version.

## Missing Connections

### [W8] No theorem connects `convergent_bisim` to `session_bisim`.

The hierarchy claims `session ⟹ convergent`, but there's no theorem proving this. `bounded_implies_session` and `bounded_implies_convergent` exist, but `session_implies_convergent` doesn't. The hierarchy diagram in the README is unproved at one of its three edges.

### [W9] No theorem connects `env_bounded_bisim` to any extension.

`Environment.lean` defines `env_bounded_bisim` and proves it corresponds to the runner. But `CrashRecovery.lean`, `EventualConsistency.lean`, `SessionConsistency.lean`, `CommutativitySpec.lean`, `EffectLattice.lean`, and `Compositional.lean` all use the environment-FREE `LockstepSystem` / `bounded_bisim`. The environment-aware versions of these extensions don't exist. The environment formalization is an island.

## Questions for the Author(s)

- **[Q1]** If `session_bisim` doesn't use session histories, what guarantees does it actually provide that `bounded_bisim` without bridge checks doesn't?

- **[Q2]** Can you construct a Lean term of type `CertifiedBridge R M` without using any `certify_*` function? If yes, the certification is ceremony, not enforcement.

- **[Q3]** The `evmap` example passes eventual consistency testing. But `convergent_bisim` in Lean requires `sys.model_sync sm = sys.sut_sync ss` at EVERY depth (including depth n+1, which checks after every action). The Rust `EventualConsistencyModel` only checks at sync points. Is there an abstraction mismatch?

## Genuinely New Research Ideas

### Idea 1: History-Indexed Session Bisimulation

Redefine `session_bisim` to thread per-session observation histories and actually CHECK `read_your_writes` and `monotonic_reads` against them. This requires dependent types on the history (or an abstract history state). Would make the session consistency formalization non-trivial.

### Idea 2: Strictness Witnesses

Construct concrete `LockstepSystem` instances that witness the strictness of each hierarchy edge. Prove in Lean: "there exists a system where `session_bisim n` holds but `bounded_bisim n` does not." This would make the hierarchy diagram a theorem, not a claim.

### Idea 3: Environment-Aware Extensions

Lift ALL extension formalizations to use `EnvLockstepSystem`. Prove `env_crash_bisim`, `env_convergent_bisim`, `env_compositional_bisim`. This would close the island problem (W9).

### Idea 4: Type-Safe Environment Encoding

Model `TypedEnv` as a dependent function `Fin n → Σ T, T` or similar, capturing that each variable slot has a specific type. Prove that `store` followed by `get` at the same index returns the stored value. This would formalize the TypedEnv beyond the current opaque abstraction.

### Idea 5: Verified Shrinking Optimality

Prove that `minimize_trace` produces the SHORTEST failing sub-trace (up to the greedy approximation). Currently there's no formal statement connecting the Rust shrinking code to the `bug_localization` theorem.

## Overall Assessment

### ICFP Pearl: **Strong Accept** (unchanged)
The bridge algebra story isn't affected by the issues above.

### POPL: **Weak Accept** (downgraded from Accept)
A hostile POPL reviewer would target W1 (session bisim is vacuous), W5 (hierarchy not proved strict), and W8 (missing edge). These are fixable but currently unfix.

### To upgrade POPL to Accept:
1. Fix `session_bisim` to actually use session histories (W1)
2. Prove hierarchy strictness with counterexamples (W5)
3. Add `session_implies_convergent` (W8)

### To upgrade POPL to Strong Accept:
4. Lift extensions to environment-aware versions (W9)
5. Type-safe environment encoding (Idea 4)
