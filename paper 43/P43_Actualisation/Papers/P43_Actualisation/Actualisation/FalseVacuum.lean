/-
  Paper 43: What the Ceiling Means
  Actualisation/FalseVacuum.lean — False vacuum decay actualisation

  BISH content: Tunnelling rate Γ/V computable from bounce action.
  Survival probability P(T) = exp(-(Γ/V)·V·T) computable.
  Detection time computable. P(survive forever) = 0.

  Actualisation: "The false vacuum eventually decays somewhere"
  = Cournot + MP. Structurally identical to radioactive decay.
-/
import Papers.P43_Actualisation.Actualisation.RadioactiveDecay
import Papers.P43_Actualisation.BISHContent.ExponentialWitness

namespace Papers.P43

noncomputable section

open Real

-- ========================================================================
-- BISH: Tunnelling detection time is computable
-- ========================================================================

/-- BISH: Tunnelling detection time is computable.
    Given rate Γ/V > 0 and tolerance ε, the detection time is explicit.
    This is a direct application of Theorem 2 with rate = Γ/V. -/
theorem tunnelling_detection_time (ΓV ε : ℝ)
    (hΓ : 0 < ΓV) (hε : 0 < ε) (hε1 : ε < 1) :
    let t₀ := detectionTime ΓV ε
    0 < t₀ ∧ exp (-ΓV * t₀) < ε :=
  detection_time_bish ΓV ε hΓ hε hε1

-- ========================================================================
-- Actualisation: The false vacuum eventually decays
-- ========================================================================

/-- Actualisation: the false vacuum eventually decays.
    Structurally identical to atom_decays_mp with rate = Γ/V.
    The logical structure is the same: BISH → Cournot → ¬∀ → MP → ∃. -/
theorem vacuum_decays_mp
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    (hMP : MarkovPrinciple)
    (tunnelled : Ω → ℕ → Bool)
    (stable : Ω → ℕ → Prop)
    (h_equiv : ∀ ω t, stable ω t ↔ tunnelled ω t = false)
    (ΓV : ℝ) (hΓ : 0 < ΓV)
    (h_model : ∀ t, μ {ω | stable ω t} =
      ENNReal.ofReal (survivalProb ΓV ↑t))
    (ω : Ω) :
    ∃ t, tunnelled ω t = true :=
  atom_decays_mp hMP tunnelled stable h_equiv ΓV hΓ h_model ω

end

end Papers.P43
