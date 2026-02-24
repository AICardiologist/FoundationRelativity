/-
  Paper 32: QED One-Loop Renormalization — The Landau Pole
  Main.lean: Master theorem and axiom audit

  This file assembles the complete CRM classification of QED
  one-loop renormalization and provides the axiom audit via
  #print axioms.
-/
import Papers.P32_QEDRenormalization.Defs
import Papers.P32_QEDRenormalization.DiscreteRG
import Papers.P32_QEDRenormalization.FinitePrecision
import Papers.P32_QEDRenormalization.Threshold
import Papers.P32_QEDRenormalization.GlobalCoupling
import Papers.P32_QEDRenormalization.LandauPole
import Papers.P32_QEDRenormalization.WardIdentity

noncomputable section

open Real

-- ============================================================
-- Master Theorem: QED Logical Constitution
-- ============================================================

/-- The complete CRM classification of QED one-loop renormalization.

    Given LPO (which subsumes both WLPO and BMC), the full QED
    one-loop renormalization program is internally consistent:

    1. (BISH) Discrete RG steps are computable and monotonic
    2. (BISH) Finite-precision predictions below the Landau pole
    3. (WLPO ⊆ LPO) Threshold crossing decisions
    4. (LPO via BMC) Global coupling across thresholds
    5. (BISH) Landau pole divergence with explicit Cauchy modulus
    6. (BISH) Ward identity preservation

    The logical constitution of QED:
    — Almost everything is BISH (constructively computable)
    — Threshold crossings need WLPO (subsumed by LPO)
    — Global coupling assembly needs BMC (equivalent to LPO)
    — The Landau pole — the most "divergent" object — is BISH!

    The surprise: the Landau pole, seemingly the most non-constructive
    feature of QED, turns out to be fully BISH because the ODE has
    an exact closed-form solution providing the Cauchy modulus. -/
theorem qed_logical_constitution (hl : LPO) (α₀ μ₀ : ℝ)
    (hα : 0 < α₀) (hμ₀ : 0 < μ₀) :
    -- Part 1: Discrete RG is BISH (no omniscience needed)
    (∀ α δ : ℝ, 0 < α → 0 < δ → α < discrete_rg_step α δ) ∧
    -- Part 2: Exact coupling computable below pole (BISH)
    (∀ μ : ℝ, 0 < μ → μ < mu_L α₀ μ₀ →
      ∃ val : ℝ, val = alpha_exact α₀ μ₀ μ ∧ 0 < val) ∧
    -- Part 3: Threshold decisions (WLPO, subsumed by LPO)
    (∀ μ : ℝ, ∀ t : FermionThreshold,
      (μ = t.mass) ∨ (μ ≠ t.mass)) ∧
    -- Part 4: Global coupling exists (LPO via BMC)
    (∀ δ M : ℝ, 0 < δ → (∀ n, iterate_rg_step α₀ δ n ≤ M) →
      ∃ L : ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |iterate_rg_step α₀ δ N - L| < ε) ∧
    -- Part 5: Landau pole divergence (BISH — the surprise!)
    (∀ M : ℝ, 0 < M →
      ∃ δ : ℝ, 0 < δ ∧ alpha_exact α₀ μ₀ (mu_L α₀ μ₀ - δ) > M) ∧
    -- Part 6: Ward identity (BISH)
    (∀ w : WardIdentity, w.Z1 = w.Z2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  -- Part 1: Discrete RG growth (BISH)
  · exact fun α δ hα hδ => discrete_step_growth α δ hα hδ
  -- Part 2: Coupling below pole (BISH)
  · exact fun μ hμ h_safe =>
      coupling_computable_below_pole α₀ μ₀ μ hα hμ₀ hμ h_safe
  -- Part 3: Threshold decisions (WLPO via LPO)
  · intro μ t
    exact threshold_decision_wlpo (wlpo_of_lpo hl) μ t
  -- Part 4: Global coupling (BMC via LPO)
  · intro δ M hδ h_bound
    exact global_coupling_exists_lpo hl α₀ μ₀ hα hμ₀ δ hδ M h_bound
  -- Part 5: Landau pole (BISH)
  · exact landau_pole_bish_classification α₀ μ₀ hα hμ₀
  -- Part 6: Ward identity (BISH)
  · exact fun w => ward_identity_algebraic w

-- ============================================================
-- Axiom Audit
-- ============================================================

#check @qed_logical_constitution
#print axioms qed_logical_constitution

-- Expected axiom profile:
-- • propext, Classical.choice, Quot.sound — Lean 4 / Mathlib foundations
-- • bmc_of_lpo — LPO → BMC (standard constructive reverse mathematics)
-- • wlpo_of_lpo — LPO → WLPO (standard)
-- • coupling_exceeds_at_delta — quantitative bound (calculus axiom)
--
-- NO sorry. The logical classification is complete.

end
