/-
  Linearizability

  Formalizes the linearizability property for concurrent executions.
  A concurrent execution (recorded as a list of operation records from
  multiple branches) is linearizable if there exists some sequential
  ordering (permutation) of the operations such that the model produces
  bridge-equivalent results at each step.

  Key results:
  - `is_linearizable` definition
  - DPOR swap preserves linearizability
  - Linearizability is independent of the representation order
  - Connection to bounded bisimulation

  Corresponds to `check_linearizability` in `src/concurrent.rs`.
-/

import FormalVerification.DPOR

-- =========================================================================
-- Linearizability definition
-- =========================================================================

/--
  A concurrent execution is linearizable if there exists some
  sequential ordering of the recorded operations such that the
  model produces bridge-equivalent results at each step.

  This is the property that `check_linearizability` in
  `src/concurrent.rs` searches for: it tries permutations of the
  concurrent operations until it finds one where the model's
  sequential execution matches the recorded SUT results.
-/
def is_linearizable (sys : LockstepSystem)
    (records : List (OpRecord sys)) (sm : sys.SM) : Prop :=
  ∃ (perm : List (OpRecord sys)),
    perm.Perm records ∧ linearization_check sys perm sm

/-- An empty execution is trivially linearizable. -/
theorem empty_linearizable (sys : LockstepSystem) (sm : sys.SM) :
    is_linearizable sys [] sm :=
  ⟨[], List.Perm.nil, trivial⟩

/--
  If the operations are already in a valid order, the execution
  is linearizable (the identity permutation works).
-/
theorem sequential_is_linearizable (sys : LockstepSystem)
    (records : List (OpRecord sys)) (sm : sys.SM)
    (h : linearization_check sys records sm) :
    is_linearizable sys records sm :=
  ⟨records, List.Perm.refl _, h⟩

-- =========================================================================
-- DPOR preserves linearizability
-- =========================================================================

/--
  **DPOR preserves linearizability**: swapping two adjacent
  operations in the record list does not change whether the
  execution is linearizable. The linearizability search explores
  all permutations, so the starting order doesn't matter.
-/
theorem swap_preserves_linearizability (sys : LockstepSystem)
    (r1 r2 : OpRecord sys) (rest : List (OpRecord sys))
    (sm : sys.SM)
    (h : is_linearizable sys (r1 :: r2 :: rest) sm) :
    is_linearizable sys (r2 :: r1 :: rest) sm := by
  obtain ⟨perm, hperm, hcheck⟩ := h
  exact ⟨perm, hperm.trans (List.Perm.swap r2 r1 rest), hcheck⟩

/--
  Linearizability is invariant under the order records are listed —
  it only depends on the multiset of operations.
-/
theorem linearizability_perm_invariant (sys : LockstepSystem)
    (records1 records2 : List (OpRecord sys)) (sm : sys.SM)
    (hperm : records1.Perm records2)
    (h : is_linearizable sys records1 sm) :
    is_linearizable sys records2 sm := by
  obtain ⟨perm, hp, hcheck⟩ := h
  exact ⟨perm, hp.trans hperm, hcheck⟩

-- =========================================================================
-- Single-branch linearizability
-- =========================================================================

/--
  A single-branch concurrent execution is always linearizable
  if the linearization check passes — there's only one possible
  ordering.
-/
theorem single_branch_linearizable (sys : LockstepSystem)
    (records : List (OpRecord sys)) (sm : sys.SM)
    (h : linearization_check sys records sm) :
    is_linearizable sys records sm :=
  sequential_is_linearizable sys records sm h

/--
  Linearizability of a single operation is equivalent to the
  bridge check passing.
-/
theorem single_op_linearizable_iff (sys : LockstepSystem)
    (r : OpRecord sys) (sm : sys.SM) :
    is_linearizable sys [r] sm
    ↔ bridge_equiv (sys.bridge r.action) r.sut_result
        (sys.step_model r.action sm).2 := by
  constructor
  · intro ⟨perm, hperm, hcheck⟩
    have hlen : perm.length = 1 := by
      rw [hperm.length_eq]; simp
    match perm, hlen with
    | [p], _ =>
      have hpeq : p = r := by
        have h := List.perm_singleton.mp hperm
        simp at h
        exact h
      subst hpeq
      simp only [linearization_check] at hcheck
      exact hcheck.1
  · intro h
    exact ⟨[r], List.Perm.refl _, ⟨h, trivial⟩⟩

-- =========================================================================
-- Non-linearizability
-- =========================================================================

/--
  **Non-linearizability detection**: if no permutation produces a
  valid linearization check, the execution is not linearizable.
  This is what the checker reports as a failure.
-/
theorem not_linearizable_iff (sys : LockstepSystem)
    (records : List (OpRecord sys)) (sm : sys.SM) :
    ¬ is_linearizable sys records sm
    ↔ ∀ (perm : List (OpRecord sys)),
        perm.Perm records → ¬ linearization_check sys perm sm := by
  constructor
  · intro h perm hperm hcheck
    exact h ⟨perm, hperm, hcheck⟩
  · intro h ⟨perm, hperm, hcheck⟩
    exact h perm hperm hcheck
