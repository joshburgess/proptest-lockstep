/-
  DPOR Soundness

  Formalizes dynamic partial-order reduction for the linearizability
  checker. The key result: swapping two adjacent commuting operations
  in a linearization preserves the validity of the linearization check.

  This justifies the sleep-set pruning in `check_linearizability_rec`:
  if two operations commute at the current model state, only one
  ordering needs to be explored.

  Corresponds to `operations_commute` and the DPOR logic in
  `src/concurrent.rs`.
-/

import FormalVerification.Lockstep

-- =========================================================================
-- Linearization checking
-- =========================================================================

/--
  A recorded operation: an action paired with its observed SUT result.
  Corresponds to `OpRecord` in `src/concurrent.rs`.
-/
structure OpRecord (sys : LockstepSystem) where
  action : sys.ActionIdx
  sut_result : sys.RetS action

/--
  Check a linearization: run the model along a sequence of recorded
  operations, checking bridge_equiv between each model result and the
  recorded SUT result. This is what the linearizability checker does
  at each candidate ordering.
-/
def linearization_check (sys : LockstepSystem) :
    List (OpRecord sys) → sys.SM → Prop
  | [], _ => True
  | r :: rest, sm =>
    bridge_equiv (sys.bridge r.action) r.sut_result (sys.step_model r.action sm).2
    ∧ linearization_check sys rest (sys.step_model r.action sm).1

/-- Empty linearization is trivially valid. -/
theorem linearization_check_nil (sys : LockstepSystem) (sm : sys.SM) :
    linearization_check sys [] sm :=
  trivial

-- =========================================================================
-- Model commutativity
-- =========================================================================

/--
  Two actions commute at a model state if executing them in either
  order yields the same per-action results and the same final state.

  Corresponds to `operations_commute` in `src/concurrent.rs`, which
  checks:
  1. Bridge equivalence of each action's result across both orderings
  2. Equality of final model states (`PartialEq`)

  This formalization uses direct equality on results (stronger than
  bridge equivalence, but sound -- equality implies bridge equivalence
  for any bridge).
-/
def model_commute (sys : LockstepSystem) (a b : sys.ActionIdx)
    (sm : sys.SM) : Prop :=
  -- Final states equal
  (sys.step_model b (sys.step_model a sm).1).1 =
    (sys.step_model a (sys.step_model b sm).1).1
  -- Result of a is the same regardless of order
  ∧ (sys.step_model a sm).2 =
    (sys.step_model a (sys.step_model b sm).1).2
  -- Result of b is the same regardless of order
  ∧ (sys.step_model b (sys.step_model a sm).1).2 =
    (sys.step_model b sm).2

/-- Commutativity is symmetric. -/
theorem commute_sym (sys : LockstepSystem) (a b : sys.ActionIdx)
    (sm : sys.SM) (h : model_commute sys a b sm) :
    model_commute sys b a sm := by
  simp only [model_commute] at h ⊢
  obtain ⟨hstate, hresult_a, hresult_b⟩ := h
  exact ⟨hstate.symm, hresult_b.symm, hresult_a.symm⟩

-- =========================================================================
-- The DPOR Soundness Theorem
-- =========================================================================

/--
  **DPOR soundness**: swapping two adjacent commuting operations in a
  linearization preserves validity.

  If the linearization check passes for `[r1, r2] ++ rest` and the
  actions of r1 and r2 commute at state `sm`, then the check also
  passes for `[r2, r1] ++ rest`.

  This is the fundamental lemma justifying DPOR sleep-set pruning:
  when the checker determines that two operations commute (via
  `operations_commute`), it can skip the swapped ordering without
  missing any valid linearization.
-/
theorem dpor_swap_sound (sys : LockstepSystem)
    (r1 r2 : OpRecord sys) (rest : List (OpRecord sys))
    (sm : sys.SM)
    (hcomm : model_commute sys r1.action r2.action sm)
    (h : linearization_check sys (r1 :: r2 :: rest) sm) :
    linearization_check sys (r2 :: r1 :: rest) sm := by
  simp only [linearization_check] at h ⊢
  simp only [model_commute] at hcomm
  obtain ⟨hbridge_a, hbridge_b, hrest⟩ := h
  obtain ⟨hstate, hresult_a, hresult_b⟩ := hcomm
  refine ⟨?_, ?_, ?_⟩
  · -- Bridge check for r2 at position 0 (running b from sm directly)
    -- Original: bridge_equiv ... (step_model b (step_model a sm).1).2
    -- Need:     bridge_equiv ... (step_model b sm).2
    -- By commutativity: these results are equal
    rw [hresult_b] at hbridge_b
    exact hbridge_b
  · -- Bridge check for r1 at position 1 (running a after b)
    -- Original: bridge_equiv ... (step_model a sm).2
    -- Need:     bridge_equiv ... (step_model a (step_model b sm).1).2
    -- By commutativity: these results are equal
    rw [hresult_a] at hbridge_a
    exact hbridge_a
  · -- Suffix: same final state, so linearization_check is identical
    -- Original: linearization_check rest (step_model b (step_model a sm).1).1
    -- Need:     linearization_check rest (step_model a (step_model b sm).1).1
    -- By commutativity: these states are equal
    rw [hstate] at hrest
    exact hrest

/--
  DPOR soundness is bidirectional: if either ordering is a valid
  linearization, so is the other.
-/
theorem dpor_swap_iff (sys : LockstepSystem)
    (r1 r2 : OpRecord sys) (rest : List (OpRecord sys))
    (sm : sys.SM)
    (hcomm : model_commute sys r1.action r2.action sm) :
    linearization_check sys (r1 :: r2 :: rest) sm
    ↔ linearization_check sys (r2 :: r1 :: rest) sm := by
  constructor
  · exact dpor_swap_sound sys r1 r2 rest sm hcomm
  · exact dpor_swap_sound sys r2 r1 rest sm (commute_sym sys r1.action r2.action sm hcomm)

-- =========================================================================
-- Prefix extension: swap at arbitrary position
-- =========================================================================

/-- Run the model through a sequence of operations, returning the final state. -/
def model_trace_state (sys : LockstepSystem) :
    List (OpRecord sys) → sys.SM → sys.SM
  | [], sm => sm
  | r :: rest, sm => model_trace_state sys rest (sys.step_model r.action sm).1

/-- Linearization check splits over append. -/
theorem linearization_check_append (sys : LockstepSystem)
    (xs ys : List (OpRecord sys)) (sm : sys.SM) :
    linearization_check sys (xs ++ ys) sm
    ↔ linearization_check sys xs sm
      ∧ linearization_check sys ys (model_trace_state sys xs sm) := by
  induction xs generalizing sm with
  | nil =>
    simp [linearization_check, model_trace_state]
  | cons r rest ih =>
    simp only [List.cons_append, linearization_check, model_trace_state]
    rw [ih]
    exact ⟨fun ⟨hb, hpre, hsuf⟩ => ⟨⟨hb, hpre⟩, hsuf⟩,
           fun ⟨⟨hb, hpre⟩, hsuf⟩ => ⟨hb, hpre, hsuf⟩⟩

/--
  **General DPOR soundness**: swapping two adjacent commuting operations
  at an arbitrary position in a linearization preserves validity.
-/
theorem dpor_swap_at (sys : LockstepSystem)
    (pre : List (OpRecord sys))
    (r1 r2 : OpRecord sys)
    (suf : List (OpRecord sys))
    (sm : sys.SM)
    (hcomm : model_commute sys r1.action r2.action
      (model_trace_state sys pre sm))
    (h : linearization_check sys (pre ++ r1 :: r2 :: suf) sm) :
    linearization_check sys (pre ++ r2 :: r1 :: suf) sm := by
  rw [linearization_check_append] at h ⊢
  obtain ⟨hpre, htail⟩ := h
  exact ⟨hpre, dpor_swap_sound sys r1 r2 suf _ hcomm htail⟩

-- =========================================================================
-- Sleep set soundness
-- =========================================================================

/--
  **Swap reachability**: `l2` is reachable from `l1` by a chain of
  adjacent commuting swaps. Each swap exchanges two adjacent elements
  that commute at the model state induced by the prefix before them.

  This is the equivalence relation that sleep sets exploit: all
  elements in a swap-reachability class produce the same
  linearization_check result, so exploring one representative suffices.
-/
inductive swap_reachable (sys : LockstepSystem) (sm : sys.SM) :
    List (OpRecord sys) → List (OpRecord sys) → Prop
  | refl (l) : swap_reachable sys sm l l
  | swap (pre : List (OpRecord sys)) (r1 r2 : OpRecord sys)
      (suf : List (OpRecord sys))
      (hcomm : model_commute sys r1.action r2.action
        (model_trace_state sys pre sm)) :
      swap_reachable sys sm
        (pre ++ r1 :: r2 :: suf) (pre ++ r2 :: r1 :: suf)
  | trans {l1 l2 l3 : List (OpRecord sys)}
      (h12 : swap_reachable sys sm l1 l2)
      (h23 : swap_reachable sys sm l2 l3) :
      swap_reachable sys sm l1 l3

/--
  **Sleep set soundness**: swap-reachable permutations produce the
  same linearization_check result. If linearization_check passes for
  one ordering, it passes for all swap-reachable orderings.

  This justifies the sleep set optimization: the DPOR checker only
  needs to explore ONE representative per swap-equivalence class.
  Operations added to the sleep set (because they commute with all
  explored operations) can be safely skipped without missing any
  linearization violation.
-/
theorem swap_reachable_sound (sys : LockstepSystem) (sm : sys.SM)
    (l1 l2 : List (OpRecord sys))
    (hreach : swap_reachable sys sm l1 l2)
    (h : linearization_check sys l1 sm) :
    linearization_check sys l2 sm := by
  induction hreach with
  | refl => exact h
  | swap pre r1 r2 suf hcomm =>
    exact dpor_swap_at sys pre r1 r2 suf sm hcomm h
  | trans _ _ ih12 ih23 =>
    exact ih23 (ih12 h)

/--
  **Swap reachability is symmetric**: if l2 is swap-reachable from l1,
  then l1 is swap-reachable from l2. Each single swap reverses via
  commutativity symmetry; chains reverse by flipping the order.
-/
theorem swap_reachable_symm (sys : LockstepSystem) (sm : sys.SM)
    (l1 l2 : List (OpRecord sys))
    (h : swap_reachable sys sm l1 l2) :
    swap_reachable sys sm l2 l1 := by
  induction h with
  | refl => exact swap_reachable.refl _
  | swap pre r1 r2 suf hcomm =>
    exact swap_reachable.swap pre r2 r1 suf
      (commute_sym sys r1.action r2.action _ hcomm)
  | trans _ _ ih12 ih23 =>
    exact swap_reachable.trans ih23 ih12

/--
  **Sleep set biconditional**: swap-reachable permutations are
  equivalent for linearization_check -- one passes iff the other does.
  This justifies exploring only one representative per
  swap-equivalence class (the sleep set optimization).
-/
theorem sleep_set_equiv (sys : LockstepSystem) (sm : sys.SM)
    (l1 l2 : List (OpRecord sys))
    (hreach : swap_reachable sys sm l1 l2) :
    linearization_check sys l1 sm ↔ linearization_check sys l2 sm :=
  ⟨swap_reachable_sound sys sm l1 l2 hreach,
   swap_reachable_sound sys sm l2 l1 (swap_reachable_symm sys sm l1 l2 hreach)⟩

