/-
  Paper 42: The Worst Prediction in Physics Is Not a Prediction
  CondensateLPO.lean: Theorem 5 — Exact interacting condensate is LPO

  The exact vacuum energy density of an interacting QFT is the
  thermodynamic limit of the lattice ground-state energy.
  The ground-state energy is subadditive in volume (from translation
  invariance). By Fekete's lemma (≡ LPO, Paper 29), the limit exists.
  The exact condensate is therefore an LPO-computable real.
-/
import Papers.P42_CosmologicalConstant.Defs

noncomputable section

-- ============================================================
-- Theorem 5: Exact interacting condensate is LPO-computable
-- ============================================================

/-- THEOREM 5: The exact interacting vacuum energy density is LPO-computable.
    The ground-state energy E(L) on a lattice of volume L is subadditive
    (bridge axiom from translation invariance). Fekete's lemma extracts
    the density ρ = lim_{L→∞} E(L)/L as the infimum of E(L)/L.
    By Paper 29 (Fekete ≡ LPO), this limit costs exactly LPO.

    Physical significance: the tree-level approximations
    ρ_Higgs ≈ −μ⁴/(4λ) and ρ_QCD ≈ −⟨q̄q⟩m_q are BISH.
    The EXACT interacting values — which include all loop corrections,
    non-perturbative effects, and vacuum fluctuations — require
    the thermodynamic limit, hence LPO. -/
theorem condensate_lpo :
    LPO → ∃ ρ_exact : ℝ,
      ∀ ε : ℝ, 0 < ε →
        ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → 0 < n →
          |lattice_vacuum_energy n / (n : ℝ) - ρ_exact| < ε := by
  intro lpo
  exact bmc_from_subadditive
    lattice_vacuum_energy lattice_energy_subadditive lattice_energy_bdd_below lpo

/-- The tree-level Higgs condensate is BISH (no LPO needed).
    It is a simple algebraic expression: V(v) = −μ⁴/(4λ). -/
theorem higgs_tree_bish : ∃ ρ_H : ℝ, ρ_H = higgs_tree_level ∧ ρ_H < 0 :=
  ⟨higgs_tree_level, rfl, higgs_tree_level_neg⟩

/-- The tree-level QCD condensate is BISH (no LPO needed).
    It is an algebraic expression: −⟨q̄q⟩ · m_q. -/
theorem qcd_tree_bish : ∃ ρ_QCD : ℝ, ρ_QCD = qcd_tree_level ∧ ρ_QCD < 0 :=
  ⟨qcd_tree_level, rfl, qcd_tree_level_neg⟩

/-- The step from BISH to LPO is the thermodynamic limit.
    At tree level (finite Feynman diagrams), condensates are BISH.
    At exact level (all orders + non-perturbative), the thermodynamic
    limit enters, and the cost jumps to LPO via Fekete. -/
theorem bish_to_lpo_is_thermodynamic_limit :
    -- BISH: tree-level condensate is an algebraic expression
    (∃ ρ_H : ℝ, ρ_H = higgs_tree_level ∧ ρ_H < 0) ∧
    -- LPO: exact interacting condensate requires thermodynamic limit
    (LPO → ∃ ρ_exact : ℝ,
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → 0 < n →
        |lattice_vacuum_energy n / (n : ℝ) - ρ_exact| < ε) := by
  exact ⟨higgs_tree_bish, condensate_lpo⟩

end
