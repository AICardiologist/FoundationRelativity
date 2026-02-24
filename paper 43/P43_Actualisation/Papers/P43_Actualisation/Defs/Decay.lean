/-
  Paper 43: What the Ceiling Means
  Defs/Decay.lean — Survival probability and detection time definitions

  Defines the mathematical objects for radioactive / false-vacuum decay:
  - survivalProb: exp(-λt), the probability of surviving to time t
  - detectionTime: (log(1/ε) + 1)/λ, the computable BISH witness
  - eternalSurvival: the set of trajectories that never decay
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Papers.P43

noncomputable section

open Real

/-- Survival probability for a Poisson process with rate λ.
    P(survive to time t) = exp(-λt). -/
def survivalProb (rate t : ℝ) : ℝ := exp (-rate * t)

/-- Computable detection time: t₀ = (log(1/ε) + 1)/λ.
    This is the BISH witness for Theorem 2. -/
def detectionTime (rate ε : ℝ) : ℝ := (log (1 / ε) + 1) / rate

/-- The set of "eternal survival" trajectories.
    An outcome ω is in this set iff the system is undecayed at every time step. -/
def eternalSurvival {Ω : Type*} (undecayed : Ω → ℕ → Prop) : Set Ω :=
  {ω | ∀ t, undecayed ω t}

end

end Papers.P43
