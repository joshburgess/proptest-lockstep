/-
  Crash-Session Observational Completeness

  Extends observational refinement to crash-session systems. A
  crash-session system satisfies crash_session_bisim iff all
  crash-interleaved traces produce matching observations with
  correct session guarantees.

  The key extension over ObservationalRefinement.lean: traces can
  include crash events that reset session histories and recover
  model/SUT state. The biconditional connects the recursive
  crash_session_bisim definition to the trace-based observational
  characterization.
-/

import Metatheory.EnvironmentExtensions

-- =========================================================================
-- Crash-interleaved traces
-- =========================================================================

/--
  A crash event in a trace: either a normal action or a crash.
  Crash events reset session histories and recover model/SUT state.
-/
inductive CrashEvent (A : Type) where
  | action : A → CrashEvent A
  | crash : CrashEvent A

/--
  Model state after running a crash-interleaved trace.
  Normal actions advance via `step_model`; crashes recover via
  `model_recover ∘ checkpoint`.
-/
def crash_model_after (sys : CrashSessionSystem) :
    List (CrashEvent sys.ActionIdx) → sys.SM → sys.SM
  | [], sm => sm
  | .action a :: rest, sm =>
    crash_model_after sys rest (sys.step_model a sm).1
  | .crash :: rest, sm =>
    crash_model_after sys rest (sys.model_recover (sys.checkpoint sm))

/--
  SUT state after running a crash-interleaved trace.
-/
def crash_sut_after (sys : CrashSessionSystem) :
    List (CrashEvent sys.ActionIdx) → sys.SS → sys.SS
  | [], ss => ss
  | .action a :: rest, ss =>
    crash_sut_after sys rest (sys.step_sut a ss).1
  | .crash :: rest, ss =>
    crash_sut_after sys rest (sys.sut_recover ss)

/--
  Session histories after running a crash-interleaved trace.
  Normal actions update write histories per session.
  Crash events reset all histories to empty.
-/
def crash_hists_after (sys : CrashSessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key] :
    List (CrashEvent sys.ActionIdx) → sys.SS →
    SessionHistories sys.Session sys.Key sys.Obs →
    SessionHistories sys.Session sys.Key sys.Obs
  | [], _, hists => hists
  | .action a :: rest, ss, hists =>
    let hists' := match sys.session_of a, sys.write_key a, sys.write_val a with
      | some s, some k, some v =>
        fun s' => if s' = s then update_write (hists s) k v else hists s'
      | _, _, _ => hists
    crash_hists_after sys rest (sys.step_sut a ss).1 hists'
  | .crash :: rest, ss, _ =>
    crash_hists_after sys rest (sys.sut_recover ss)
      (empty_histories sys.Session sys.Key sys.Obs)

-- =========================================================================
-- Crash-session observational equivalence
-- =========================================================================

/--
  **Crash-session observational equivalence**: after any
  crash-interleaved prefix of depth ≤ n, the system satisfies:
  1. Bridge observations match for any action
  2. RYW holds for any read action (given accumulated history)
  3. The model invariant holds
-/
def crash_session_obs_equiv (sys : CrashSessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (hists : SessionHistories sys.Session sys.Key sys.Obs) : Prop :=
  ∀ (trace : List (CrashEvent sys.ActionIdx)),
    trace.length + 1 ≤ n →
    let sm' := crash_model_after sys trace sm
    let ss' := crash_sut_after sys trace ss
    let hists' := crash_hists_after sys trace ss hists
    -- Invariant at current state
    sys.invariant sm'
    -- Bridge + RYW for every action at the post-prefix state
    ∧ ∀ (a : sys.ActionIdx),
      bridge_equiv (sys.bridge a)
        (sys.step_sut a ss').2 (sys.step_model a sm').2
      ∧ (match sys.session_of a, sys.read_key a, sys.sut_read_obs a ss' with
        | some s, some k, some obs => read_your_writes (hists' s) k obs
        | _, _, _ => True)

-- =========================================================================
-- Forward direction: bisim → observational equivalence
-- =========================================================================

/--
  **Forward**: crash_session_bisim implies crash_session_obs_equiv.
  If the bisimulation holds, all crash-interleaved traces produce
  matching observations.
-/
theorem crash_session_bisim_implies_obs (sys : CrashSessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (hists : SessionHistories sys.Session sys.Key sys.Obs)
    (h : crash_session_bisim sys n sm ss hists) :
    crash_session_obs_equiv sys n sm ss hists := by
  intro trace hdepth
  induction trace generalizing sm ss hists n with
  | nil =>
    simp [crash_model_after, crash_sut_after, crash_hists_after]
    match n, hdepth with
    | n' + 1, _ =>
      simp only [crash_session_bisim] at h
      obtain ⟨hinv, hactions, _⟩ := h
      exact ⟨hinv, fun a => ⟨(hactions a).2.1, (hactions a).1⟩⟩
  | cons ev rest ih =>
    match ev with
    | .action a =>
      simp only [crash_model_after, crash_sut_after, crash_hists_after]
      match n, hdepth with
      | n' + 1, hdepth' =>
        simp only [crash_session_bisim] at h
        obtain ⟨_, hactions, _⟩ := h
        have ha := hactions a
        exact ih n' _ _ _ ha.2.2 (by simp at hdepth'; omega)
    | .crash =>
      simp only [crash_model_after, crash_sut_after, crash_hists_after]
      match n, hdepth with
      | n' + 1, hdepth' =>
        simp only [crash_session_bisim] at h
        obtain ⟨_, _, hcrash⟩ := h
        exact ih n' _ _ _ hcrash (by simp at hdepth'; omega)

-- =========================================================================
-- Backward direction: observational equivalence → bisim
-- =========================================================================

/--
  **Backward**: crash_session_obs_equiv implies crash_session_bisim.
  If all crash-interleaved traces produce matching observations,
  the bisimulation holds. This is the harder direction.

  The proof follows the pattern of `observational_refinement_equiv`:
  - Empty trace gives the current-step obligations (invariant, bridge, RYW)
  - Action-prefixed trace gives the successor obligation
  - Crash-prefixed trace gives the crash-recovery obligation
-/
theorem crash_session_obs_implies_bisim (sys : CrashSessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (hists : SessionHistories sys.Session sys.Key sys.Obs)
    (h : crash_session_obs_equiv sys n sm ss hists) :
    crash_session_bisim sys n sm ss hists := by
  induction n generalizing sm ss hists with
  | zero => trivial
  | succ k ih =>
    simp only [crash_session_bisim]
    -- Get current-step obligations from empty trace
    have h_empty := h [] (by simp)
    simp [crash_model_after, crash_sut_after, crash_hists_after] at h_empty
    obtain ⟨hinv, hcurrent⟩ := h_empty
    refine ⟨hinv, ?_, ?_⟩
    · -- Normal actions
      intro a
      have ⟨hbridge, hryw⟩ := hcurrent a
      refine ⟨hryw, hbridge, ?_⟩
      -- Successor bisim: use ih with action-prefixed traces
      apply ih
      intro trace hdepth
      have := h (.action a :: trace) (by simp; omega)
      simp [crash_model_after, crash_sut_after, crash_hists_after] at this
      exact this
    · -- Crash recovery: use ih with crash-prefixed traces
      apply ih
      intro trace hdepth
      have := h (.crash :: trace) (by simp; omega)
      simp [crash_model_after, crash_sut_after, crash_hists_after] at this
      exact this

-- =========================================================================
-- The biconditional
-- =========================================================================

/--
  **Crash-session observational completeness**: crash_session_bisim
  at depth n is equivalent to crash_session_obs_equiv at depth n.

  This extends `observational_refinement_equiv` to crash-session
  systems: the recursive bisimulation definition and the trace-based
  observational characterization are the same property, now with
  crash events that reset session histories.

  Combined with crash_session_implies_crash and
  crash_session_implies_bounded, this gives the full picture:

    crash_session_bisim ↔ crash_session_obs_equiv
    crash_session_bisim → crash_bisim → bounded_bisim
-/
theorem crash_session_obs_equiv_iff (sys : CrashSessionSystem)
    [DecidableEq sys.Session] [DecidableEq sys.Key]
    (n : Nat) (sm : sys.SM) (ss : sys.SS)
    (hists : SessionHistories sys.Session sys.Key sys.Obs) :
    crash_session_bisim sys n sm ss hists
    ↔ crash_session_obs_equiv sys n sm ss hists :=
  ⟨crash_session_bisim_implies_obs sys n sm ss hists,
   crash_session_obs_implies_bisim sys n sm ss hists⟩
