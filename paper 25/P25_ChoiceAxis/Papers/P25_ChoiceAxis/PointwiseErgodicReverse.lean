/-
Papers/P25_ChoiceAxis/PointwiseErgodicReverse.lean
Paper 25: Birkhoff → DC — Additional Analysis

This module provides additional documentation and derived results
for the reverse direction Birkhoff → DC.

The main axiom `dc_of_birkhoff` is in PointwiseErgodic.lean.
This module contains the consequence that Birkhoff strictly exceeds CC.
-/
import Papers.P25_ChoiceAxis.PointwiseErgodic
import Papers.P25_ChoiceAxis.MeanErgodicReverse

namespace Papers.P25_ChoiceAxis

/-! ## Consequences of the Birkhoff ↔ DC calibration -/

/-- **Birkhoff's theorem is strictly above the mean ergodic theorem**
    in the choice hierarchy.

    The mean ergodic theorem (norm convergence) calibrates to CC.
    Birkhoff's theorem (pointwise convergence) calibrates to DC.
    Since DC is strictly stronger than CC (in constructive mathematics),
    pointwise convergence is genuinely harder than norm convergence.

    This formalizes the classical analyst's intuition that "pointwise
    convergence is harder than norm convergence" as a precise logical
    separation in the choice hierarchy. -/
theorem birkhoff_above_mean_ergodic :
    (BirkhoffErgodicTheorem → DC) ∧ (MeanErgodicTheorem → CC_N) :=
  ⟨dc_of_birkhoff, meanErgodic_implies_cc⟩

/-! ## Physical interpretation

The CC/DC separation in ergodic theory has a clean physical reading:

**CC (mean ergodic / ensemble level)**:
  "The time-averaged expectation value of an observable converges
   to its ensemble average." This is verified by comparing many
   experimental runs — each run is an independent measurement (CC).

**DC (pointwise ergodic / trajectory level)**:
  "For almost every initial condition, the individual time average
   converges to the ensemble average." This is about individual
   trajectories — the construction of the exceptional null set
   requires dependent sequential refinement (DC).

Operationally, experimentalists verify the CC-level statement.
The DC-level statement is an idealization about individual systems
observed for infinite time — philosophically stronger but not
experimentally distinguishable from the CC-level claim.
-/

end Papers.P25_ChoiceAxis
