-- Formal Verification of Lockstep Testing
--
-- This project formalizes the metatheory of proptest-lockstep:
-- the bridge algebra as a logical relation, the lockstep
-- bisimulation, and soundness theorems.

import FormalVerification.Bridge
import FormalVerification.BridgeRefinement
import FormalVerification.CommutativitySpec
import FormalVerification.CrashRecovery
import FormalVerification.EventualConsistency
import FormalVerification.SessionConsistency
import FormalVerification.Invariant
import FormalVerification.DPOR
import FormalVerification.EffectLattice
import FormalVerification.DerivedBridge
import FormalVerification.Linearizability
import FormalVerification.Lockstep
import FormalVerification.ObservationalRefinement
import FormalVerification.OpaqueDetection
import FormalVerification.Precondition
import FormalVerification.Runner
import FormalVerification.Soundness
import FormalVerification.TestingCompleteness
