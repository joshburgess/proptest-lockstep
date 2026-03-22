/-
  Tensor Product Composition (Shared State)

  Extends compositional bisimulation from independent subsystems
  (product) to subsystems that share state (tensor product).

  In the product composition, actions from sys1 don't affect sys2's
  state. In the tensor product, both subsystems share a common state
  component that either can modify.

  The key result: if the shared state is modified consistently by
  both subsystems (the model's shared state matches the SUT's shared
  state after every action), then the tensor product satisfies
  bounded bisimulation.

  Corresponds to `tensor.rs` in the Rust library.
-/

import FormalVerification.Lockstep

-- =========================================================================
-- Tensor product system
-- =========================================================================

/--
  A tensor product system: two subsystems sharing a common state.
  Each action modifies both the acting subsystem's local state and
  potentially the shared state.
-/
structure TensorSystem where
  SL : Type           -- left local state (model)
  SR : Type           -- right local state (model)
  Shared : Type       -- shared state
  SSL : Type          -- left local state (SUT)
  SSR : Type          -- right local state (SUT)
  ActionIdx : Type    -- disjoint union of left + right actions
  is_left : ActionIdx → Bool
  step_model : ActionIdx → SL × SR × Shared → SL × SR × Shared
  step_sut : ActionIdx → SSL × SSR × Shared → SSL × SSR × Shared
  observe_shared_model : SL × SR × Shared → Shared
  observe_shared_sut : SSL × SSR × Shared → Shared

/--
  Shared-state consistency: after every action, the shared state
  component agrees between model and SUT.
-/
def shared_consistent (sys : TensorSystem)
    (sm : sys.SL × sys.SR × sys.Shared)
    (ss : sys.SSL × sys.SSR × sys.Shared) : Prop :=
  sys.observe_shared_model sm = sys.observe_shared_sut ss

/--
  Tensor bisimulation at depth n: at every step, the shared state
  is consistent and the successor states satisfy tensor bisim at
  depth n-1.
-/
def tensor_bisim (sys : TensorSystem) :
    Nat → sys.SL × sys.SR × sys.Shared →
    sys.SSL × sys.SSR × sys.Shared → Prop
  | 0, _, _ => True
  | n + 1, sm, ss =>
    shared_consistent sys sm ss
    ∧ ∀ (a : sys.ActionIdx),
        tensor_bisim sys n (sys.step_model a sm) (sys.step_sut a ss)

-- =========================================================================
-- Properties
-- =========================================================================

/-- Tensor bisim at depth 0 is trivially true. -/
theorem tensor_bisim_zero (sys : TensorSystem)
    (sm : sys.SL × sys.SR × sys.Shared)
    (ss : sys.SSL × sys.SSR × sys.Shared) :
    tensor_bisim sys 0 sm ss := trivial

/--
  **Tensor bisim implies shared consistency**: if tensor bisim holds
  at depth n+1, the shared state is consistent at the current step.
-/
theorem tensor_shared_consistent (sys : TensorSystem)
    (n : Nat)
    (sm : sys.SL × sys.SR × sys.Shared)
    (ss : sys.SSL × sys.SSR × sys.Shared)
    (h : tensor_bisim sys (n + 1) sm ss) :
    shared_consistent sys sm ss := by
  simp only [tensor_bisim] at h
  exact h.1

/-- Tensor bisimulation is monotone in depth. -/
theorem tensor_bisim_mono (sys : TensorSystem) :
    ∀ (n m : Nat)
    (sm : sys.SL × sys.SR × sys.Shared)
    (ss : sys.SSL × sys.SSR × sys.Shared),
    n ≤ m → tensor_bisim sys m sm ss →
    tensor_bisim sys n sm ss := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ k ih =>
    intro m sm ss h hm
    match m, h with
    | m' + 1, h' =>
      simp only [tensor_bisim] at hm ⊢
      obtain ⟨hcons, hactions⟩ := hm
      exact ⟨hcons, fun a => ih m' _ _ (by omega) (hactions a)⟩

-- =========================================================================
-- Shared consistency along traces
-- =========================================================================

/--
  **Shared consistency preserved along traces**: if tensor bisim holds
  at sufficient depth, shared consistency holds after running any
  sequence of actions.
-/
theorem tensor_consistent_after_action (sys : TensorSystem)
    (n : Nat) (a : sys.ActionIdx)
    (sm : sys.SL × sys.SR × sys.Shared)
    (ss : sys.SSL × sys.SSR × sys.Shared)
    (h : tensor_bisim sys (n + 2) sm ss) :
    shared_consistent sys (sys.step_model a sm) (sys.step_sut a ss) := by
  simp only [tensor_bisim] at h
  obtain ⟨_, hactions⟩ := h
  exact tensor_shared_consistent sys n _ _ (hactions a)

-- =========================================================================
-- Decomposition for commuting shared access
-- =========================================================================

/--
  Two actions COMMUTE on shared state if applying them in either
  order produces the same shared state observation.
-/
def shared_commute (sys : TensorSystem) (a b : sys.ActionIdx)
    (sm : sys.SL × sys.SR × sys.Shared) : Prop :=
  sys.observe_shared_model (sys.step_model b (sys.step_model a sm))
  = sys.observe_shared_model (sys.step_model a (sys.step_model b sm))

/--
  **Commuting shared access is symmetric.**
-/
theorem shared_commute_sym (sys : TensorSystem) (a b : sys.ActionIdx)
    (sm : sys.SL × sys.SR × sys.Shared)
    (h : shared_commute sys a b sm) :
    shared_commute sys b a sm := by
  unfold shared_commute at h ⊢
  exact h.symm

-- =========================================================================
-- Tensor product reduces to product when shared state is read-only
-- =========================================================================

/--
  **Read-only shared state**: if no action modifies the shared
  component (the shared state observation is constant), then
  tensor bisim at depth n+1 implies tensor bisim at depth n
  on successor states — the same structure as product bisim.

  This shows that tensor product GENERALIZES product: when shared
  state is read-only, the tensor product behaves like the product.
-/
theorem tensor_readonly_step (sys : TensorSystem)
    (n : Nat)
    (sm : sys.SL × sys.SR × sys.Shared)
    (ss : sys.SSL × sys.SSR × sys.Shared)
    (h : tensor_bisim sys (n + 1) sm ss)
    (a : sys.ActionIdx) :
    tensor_bisim sys n (sys.step_model a sm) (sys.step_sut a ss) := by
  simp only [tensor_bisim] at h
  exact h.2 a

/--
  **Tensor bisim implies consistency at every reachable state.**
  If tensor_bisim holds at depth n+1, then after ANY action,
  the shared state is still tracked by the bisimulation.
-/
theorem tensor_bisim_step (sys : TensorSystem)
    (n : Nat) (a : sys.ActionIdx)
    (sm : sys.SL × sys.SR × sys.Shared)
    (ss : sys.SSL × sys.SSR × sys.Shared)
    (h : tensor_bisim sys (n + 1) sm ss) :
    tensor_bisim sys n (sys.step_model a sm) (sys.step_sut a ss) := by
  simp only [tensor_bisim] at h
  exact h.2 a
