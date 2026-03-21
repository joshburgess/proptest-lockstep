# lambda-bridge: A Typed Calculus for Lockstep Testing

## Motivation

The proptest-lockstep library encodes three interacting formal systems within Rust's type system:

1. A **bridge algebra** that defines type-indexed relations between "real" and "model" domains
2. A **phase distinction** that separates symbolic generation from concrete execution
3. A **projection language** for decomposing compound return types

These are currently encoded via Rust traits, GATs, and Leibniz equality witnesses. A formal calculus makes the invariants explicit and enables metatheoretic reasoning.


## Syntax

### Types

```
tau ::= Unit                        -- unit type
      | tau_1 x tau_2               -- products
      | tau_1 + tau_2               -- sums (Result/Either)
      | tau?                        -- option (1 + tau)
      | [tau]                       -- lists (Vec)
      | Var[p, tau]                 -- phase-indexed variable reference
      | tau_1 -/-> tau_2            -- partial projection (Op)

p ::= S                            -- symbolic phase
    | C                            -- concrete phase

beta ::= Delta(tau)                 -- transparent bridge (identity)
       | Top(tau_R, tau_M)          -- opaque bridge (trivial)
       | beta_1 + beta_2           -- sum bridge
       | beta_1 x beta_2           -- product bridge
       | beta?                     -- option bridge
       | [beta]                    -- list bridge
```

### Bridge Formation

A bridge beta relates three types: Real(beta), Model(beta), and Obs(beta).

```
Real(Delta(tau))     = tau       Model(Delta(tau))     = tau       Obs(Delta(tau))     = tau
Real(Top(R,M))       = R        Model(Top(R,M))       = M        Obs(Top(R,M))       = Unit
Real(b1 + b2)        = Real(b1) + Real(b2)
Model(b1 + b2)       = Model(b1) + Model(b2)
Obs(b1 + b2)         = Obs(b1) + Obs(b2)
Real(b1 x b2)        = Real(b1) x Real(b2)
Model(b1 x b2)       = Model(b1) x Model(b2)
Obs(b1 x b2)         = Obs(b1) x Obs(b2)
Real(b?)             = Real(b)?
Model(b?)            = Model(b)?
Obs(b?)              = Obs(b)?
Real([b])            = [Real(b)]
Model([b])           = [Model(b)]
Obs([b])             = [Obs(b)]
```

### Terms

```
e ::= ()                           -- unit
    | (e_1, e_2)                   -- pair
    | fst e | snd e                -- projections
    | inl e | inr e                -- injections
    | case e of inl x -> e_1; inr x -> e_2  -- case
    | some e | none                -- option constructors
    | [] | e :: e                  -- list constructors
    | x                            -- variable
    | var[n]                       -- symbolic variable reference (phase S)
    | val(v)                       -- concrete value wrapper (phase C)
    | pi . e                       -- projection application (partial)
    | pi_1 ; pi_2                  -- projection composition
    | observe_R(beta, e)           -- real observation
    | observe_M(beta, e)           -- model observation
    | check(beta, e_R, e_M)       -- bridge check (decidable)
    | let x = step(a, s) in e    -- action execution (monadic)
    | resolve(var[n], pi, Sigma)  -- environment lookup + projection (maybe)
```

### Projections (the Op language)

```
pi ::= id                          -- identity: tau -/-> tau
     | fst                         -- first:    tau_1 x tau_2 -/-> tau_1
     | snd                         -- second:   tau_1 x tau_2 -/-> tau_2
     | ok                          -- ok:       tau_1 + tau_2 -/-> tau_1
     | err                         -- err:      tau_1 + tau_2 -/-> tau_2
     | some_p                      -- some:     tau? -/-> tau
     | idx(n)                      -- index:    [tau] -/-> tau
     | pi_1 ; pi_2                 -- compose:  (tau_1 -/-> tau_2) ; (tau_2 -/-> tau_3) = tau_1 -/-> tau_3
```


## Typing Rules

### Bridge Well-formedness

```
                                ------------- [B-Trans]
                                |- Delta(tau) bridge


                                --------------- [B-Opaque]
                                |- Top(R, M) bridge


     |- b1 bridge    |- b2 bridge
     ----------------------------- [B-Sum]
          |- b1 + b2 bridge


     |- b1 bridge    |- b2 bridge
     ----------------------------- [B-Prod]
          |- b1 x b2 bridge


            |- b bridge
          --------------- [B-Opt]
            |- b? bridge


            |- b bridge
          --------------- [B-List]
            |- [b] bridge
```

### Observation Typing

```
     |- beta bridge    Gamma |- e : Real(beta)
     ------------------------------------------ [T-ObsR]
         Gamma |- observe_R(beta, e) : Obs(beta)


     |- beta bridge    Gamma |- e : Model(beta)
     ------------------------------------------- [T-ObsM]
         Gamma |- observe_M(beta, e) : Obs(beta)
```

### Bridge Equivalence (the key judgment)

```
r ~_{beta} m   <=>   observe_R(beta, r) = observe_M(beta, m)
```

### Projection Typing

```
          ------------- [P-Id]
          |- id : tau -/-> tau


          ----------------------- [P-Fst]
          |- fst : tau_1 x tau_2 -/-> tau_1


          ----------------------- [P-Snd]
          |- snd : tau_1 x tau_2 -/-> tau_2


          ----------------------- [P-Ok]
          |- ok : tau_1 + tau_2 -/-> tau_1


          ----------------------- [P-Err]
          |- err : tau_1 + tau_2 -/-> tau_2


          ------------------- [P-Some]
          |- some_p : tau? -/-> tau


          -------------------- [P-Idx]
          |- idx(n) : [tau] -/-> tau


     |- pi_1 : tau_1 -/-> tau_2    |- pi_2 : tau_2 -/-> tau_3
     ---------------------------------------------------------- [P-Comp]
                    |- pi_1 ; pi_2 : tau_1 -/-> tau_3
```

### Phase-Indexed Variables

```
     ---------------------------------- [T-SymVar]
     Gamma, var[n] : tau |-_S var[n] : Var[S, tau]


     ---------------------------------- [T-ConVar]
     Gamma |-_C val(v) : Var[C, tau]   when v : tau
```

The phase subscript on the turnstile (`|-_S` vs `|-_C`) prevents symbolic terms from appearing in concrete contexts and vice versa.

### Generalized Variable (GVar)

```
     Gamma |-_S var[n] : Var[S, X]    |- pi : X -/-> Y
     --------------------------------------------------- [T-GVar]
           Gamma |-_S gvar(n, pi) : GVar[X, Y]
```

### Resolution

```
     Gamma |-_S gvar(n, pi) : GVar[X, Y]    Sigma |- n |-> v : X
     -------------------------------------------------------------- [T-Resolve]
                    Gamma; Sigma |- resolve(n, pi) : Y?
```

Where Sigma is the runtime environment (TypedEnv).


## Operational Semantics (Small-step)

### Observation Reduction

```
     observe_R(Delta(tau), v)  -->  v                                   [E-ObsR-Trans]

     observe_R(Top(R,M), v)  -->  ()                                    [E-ObsR-Opaque]

     observe_R(b1 + b2, inl v)  -->  inl (observe_R(b1, v))            [E-ObsR-SumL]

     observe_R(b1 + b2, inr v)  -->  inr (observe_R(b2, v))            [E-ObsR-SumR]

     observe_R(b1 x b2, (v1, v2))  -->  (observe_R(b1, v1), observe_R(b2, v2))  [E-ObsR-Prod]

     observe_R(b?, some v)  -->  some (observe_R(b, v))                 [E-ObsR-Some]

     observe_R(b?, none)  -->  none                                      [E-ObsR-None]

     observe_R([b], [])  -->  []                                         [E-ObsR-Nil]

     observe_R([b], v :: vs)  -->  observe_R(b, v) :: observe_R([b], vs) [E-ObsR-Cons]
```

(Model observation rules are symmetric, replacing R with M everywhere.)

### Projection Reduction

```
     id . v  -->  some v                                  [E-ProjId]

     fst . (v1, v2)  -->  some v1                        [E-ProjFst]

     snd . (v1, v2)  -->  some v2                        [E-ProjSnd]

     ok . inl v  -->  some v                              [E-ProjOk-L]

     ok . inr v  -->  none                                [E-ProjOk-R]

     err . inl v  -->  none                               [E-ProjErr-L]

     err . inr v  -->  some v                             [E-ProjErr-R]

     some_p . some v  -->  some v                         [E-ProjSome-S]

     some_p . none  -->  none                             [E-ProjSome-N]

     (pi_1 ; pi_2) . v  -->  case pi_1 . v of
                                some w -> pi_2 . w
                                none   -> none            [E-ProjComp]
```

### Resolution Reduction

```
     Sigma(n) = v    pi . v --> some w
     --------------------------------- [E-Resolve-Ok]
     resolve(n, pi, Sigma) --> some w

     Sigma(n) = v    pi . v --> none
     --------------------------------- [E-Resolve-Fail]
     resolve(n, pi, Sigma) --> none

     n not in dom(Sigma)
     --------------------------------- [E-Resolve-Missing]
     resolve(n, pi, Sigma) --> none
```

### Bridge Check Reduction

```
     observe_R(beta, r) = observe_M(beta, m)
     ---------------------------------------- [E-Check-Ok]
     check(beta, r, m)  -->  ok

     observe_R(beta, r) != observe_M(beta, m)
     ---------------------------------------- [E-Check-Fail]
     check(beta, r, m)  -->  err(obs_R, obs_M)
```


## Lockstep Execution System

### System Definition

A lockstep system is a tuple:

```
Sys = (SM, SS, Act, RetR, RetM, bridge, stepM, stepS)
```

where:
- SM, SS: state types (model, SUT)
- Act: action index type
- RetR, RetM: Act -> Type (dependent return types)
- bridge: (a : Act) -> Bridge(RetR(a), RetM(a))
- stepM: (a : Act) -> SM -> SM x RetM(a)
- stepS: (a : Act) -> SS -> SS x RetR(a)

### Bounded Bisimulation

```
bisim(Sys, 0, sm, ss) = True

bisim(Sys, n+1, sm, ss) = forall a : Act.
    let (sm', rm) = stepM(a, sm)
    let (ss', rs) = stepS(a, ss)
    rs ~_{bridge(a)} rm  /\  bisim(Sys, n, sm', ss')
```

### Runner Judgment

The key operational judgment for the test runner:

```
     sm0, ss0 |- [] |>_b (sm0, ss0, Sigma0)              [R-Empty]

     stepM(a, sm) = (sm', rm)
     stepS(a, ss) = (ss', rs)
     check(bridge(a), rs, rm) = ok
     sm', ss' |- as |>_b (sm'', ss'', Sigma')
     ----------------------------------------- [R-Step]
     sm, ss |- (a :: as) |>_b (sm'', ss'', Sigma'[n |-> rs])
```


## Metatheorems

### Theorem 1: Fundamental Theorem of Bridge Equivalence

Each algebraic lift preserves bridge equivalence:

(a) If `r ~_{b1} m` then `inl(r) ~_{b1+b2} inl(m)`.
(b) If `r ~_{b2} m` then `inr(r) ~_{b1+b2} inr(m)`.
(c) If `r1 ~_{b1} m1` and `r2 ~_{b2} m2` then `(r1,r2) ~_{b1 x b2} (m1,m2)`.
(d) If `r ~_b m` then `Some(r) ~_{b?} Some(m)`.
(e) `None ~_{b?} None`.
(f) If `ri ~_b mi` for all i, then `[r1,...,rn] ~_{[b]} [m1,...,mn]`.

This is proved for each bridge constructor in Bridge.lean.

### Theorem 2: Bridge Observation Determinism

For any bridge beta and value v : Real(beta), observe_R(beta, v) reduces to a unique value. Similarly for observe_M.

Proof sketch: By structural induction on beta. Each observation rule is deterministic (no overlapping patterns).

### Theorem 3: Projection Totality for Total Projections

If pi : tau_1 -/-> tau_2 is a "total" projection (id, fst, snd) and v : tau_1, then pi . v = some w for some w : tau_2.

If pi is "partial" (ok, err, some_p, idx), then pi . v = some w or pi . v = none.

### Theorem 4: Phase Soundness

If Gamma |-_S e : tau, then e contains no concrete values (val(v) subterms).
If Gamma |-_C e : tau, then e contains no symbolic variables (var[n] subterms).

This captures the Phase GAT's guarantee: symbolic and concrete worlds don't mix.

### Theorem 5: Runner Soundness (the key theorem, NOT yet proved in Lean)

If sm0, ss0 |- [a1, ..., an] |>_b (smn, ssn, Sigma), then bisim(Sys, n, sm0, ss0).

Proof sketch: By induction on n. At each step, [R-Step] ensures check(bridge(ai), rsi, rmi) = ok, which by the bridge check semantics means observe_R(bridge(ai), rsi) = observe_M(bridge(ai), rmi), which is exactly rsi ~_{bridge(ai)} rmi.

**This is the theorem the Lean formalization should prove.** The calculus makes the statement precise: the runner's step-by-step execution (|>_b judgment) implies the bisimulation relation (bisim).

### Theorem 6: Projection-Bridge Compatibility

If beta has structure (e.g., b1 x b2) and pi is a compatible projection (e.g., fst), then:
If r ~_{b1 x b2} m, then (fst . r) ~_{b1} (fst . m) whenever both projections succeed.

This connects the projection language to the bridge algebra: projections preserve bridge equivalence when the bridge structure matches the projection structure.

### Theorem 7: Monotonicity (proved in Lean)

If bisim(Sys, m, sm, ss) and n <= m, then bisim(Sys, n, sm, ss).

### Theorem 8: Opaque Handle Eventual Detection

If the SUT returns a "wrong" handle (opaque bridge passes at depth k), and the handle is used in a subsequent action at depth k+j with a transparent bridge, then the bisimulation fails at depth k+j.

More precisely:

```
If not(r_handle corresponds_to m_handle) at depth k (but Top passes),
and at depth k+j, action a uses the handle and
bridge(a) has transparent components depending on the handle,
then not bisim(Sys, k+j, sm_k, ss_k).
```

This captures what theory.rs states informally about opacity and behavioral equivalence.


## What This Calculus Reveals

1. **The bridge algebra is a free logical relation.** Given a set of base bridges (Delta and Top), the type constructors (+, x, ?, []) generate all composite bridges for free. The fundamental theorem says this free generation preserves the relational structure.

2. **The projection language is the Kleisli category of Maybe.** `Op` is exactly partial functions with failure. The composition `pi_1 ; pi_2` is Kleisli composition. The `GVar` bundles a name with a morphism in this category.

3. **The phase distinction is a modal separation.** The |-_S and |-_C turnstiles prevent mixing -- this is a two-world modal system where S is "future" (code) and C is "now" (value).

4. **The missing theorem is Runner Soundness (Theorem 5).** The Lean formalization proves properties of the bisimulation relation and the bridge algebra, but doesn't connect them to the operational runner. The calculus makes the gap precise: the [R-Step] judgment needs to be shown to imply bisim.

5. **Projection-bridge compatibility (Theorem 6) is needed for opaque handle correctness.** The claim that wrong handles are "eventually detected" depends on projections preserving bridge structure -- if you project out the opaque component and use it with a transparent bridge, the transparent bridge catches the mismatch.


## Example: File System in lambda-bridge

```
-- Types
FileHandle : Type_R          -- real handle
MockHandle : Type_M          -- model handle
FsErr = NotFound | AlreadyOpen | BadHandle

-- Bridge for Open
beta_open = (Top(FileHandle, MockHandle) x Delta(String)) + Delta(FsErr)

-- A symbolic reference to the handle from a prior Open:
handle_var : GVar[Result<(FileHandle, String), FsErr>, FileHandle]
handle_var = gvar(0, ok ; fst)

-- Resolving at runtime:
resolve(0, ok ; fst, Sigma)
  --> case (ok . Sigma(0)) of
        some (h, p) -> fst . (h, p) -> some h
        none        -> none

-- Bridge check for a Write result:
check(Delta(()) + Delta(FsErr), real_result, model_result)
  --> observe_R(Delta(()) + Delta(FsErr), real_result) =? observe_M(...)
```
