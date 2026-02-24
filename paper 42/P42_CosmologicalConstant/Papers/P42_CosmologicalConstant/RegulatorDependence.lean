/-
  Paper 42: The Worst Prediction in Physics Is Not a Prediction
  RegulatorDependence.lean: Theorem 2 — Different regularizers yield different values

  The absolute vacuum energy depends on the choice of regularization scheme.
  Cutoff regularization gives ~Λ_UV⁴/(16π²); dimensional regularization
  gives ~m⁴ ln(m²/μ²). These are numerically different.
  A quantity that changes with the scaffolding is not a physical prediction.

  BISH: the proof uses only the bridge axiom asserting inequality of two
  specific regularized values. No limits, no omniscience principles.
-/
import Papers.P42_CosmologicalConstant.Defs

noncomputable section

-- ============================================================
-- Theorem 2: The absolute vacuum energy is regulator-dependent
-- ============================================================

/-- THEOREM 2: The absolute vacuum energy is regulator-dependent.
    There exist two valid regularization schemes that yield
    different numerical values for the vacuum energy density.

    Physical significance: the "prediction" ρ_vac ~ 10⁷¹ GeV⁴ arises
    only under cutoff regularization. Dimensional regularization, which
    preserves gauge and Lorentz invariance, produces a qualitatively
    different (and much smaller) value. The "worst prediction in physics"
    is an artifact of the scaffolding choice.

    BISH: the proof is direct from the bridge axiom. -/
theorem prediction_regulator_dependent :
    ∃ (r₁ r₂ : RegScheme),
      regularized_vacuum_energy r₁ ≠ regularized_vacuum_energy r₂ := by
  obtain ⟨Λ_UV, hΛ, μ, hμ, hne⟩ := dimreg_value_different
  exact ⟨RegScheme.cutoff Λ_UV hΛ, RegScheme.dimreg μ hμ, hne⟩

/-- Corollary: no regulator-invariant absolute vacuum energy exists.
    If the value depends on the scheme, it cannot represent a physical observable. -/
theorem no_regulator_invariant_vacuum_energy :
    ¬ ∃ (ρ : ℝ), ∀ r : RegScheme, regularized_vacuum_energy r = ρ := by
  intro ⟨ρ, hinv⟩
  obtain ⟨Λ_UV, hΛ, μ, hμ, hne⟩ := dimreg_value_different
  exact hne (by rw [hinv, hinv])

/-- The 10¹²⁰ discrepancy is a property of cutoff regularization,
    not of QFT. Cutoff gives a large positive number; dim. reg.
    gives a different value. The "discrepancy" is the difference
    between a scaffolding artifact and the observed value. -/
theorem cutoff_artifact (Λ_UV : ℝ) (hΛ : 0 < Λ_UV) :
    regularized_vacuum_energy (RegScheme.cutoff Λ_UV hΛ) > 0 :=
  cutoff_gives_quartic Λ_UV hΛ

end
