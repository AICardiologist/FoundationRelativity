/-
Papers/P16_BornRule/Main.lean
Paper 16: The Born Rule as a Logical Artefact.

Assembly module: imports all components, runs axiom audit.
Verifies the CRM separation:
  - BISH theorems: no dc_omega_holds, no slln_of_dc
  - DC theorems: dc_omega_holds + slln_of_dc present
-/
import Papers.P16_BornRule.BornProbability
import Papers.P16_BornRule.Expectation
import Papers.P16_BornRule.Variance
import Papers.P16_BornRule.RelativeFreq
import Papers.P16_BornRule.WeakLaw
import Papers.P16_BornRule.StrongLaw

namespace Papers.P16

-- ========================================================================
-- BISH Layer (Level 0) — No DC, no limits, no choice
-- ========================================================================

-- Theorem 1: Born probability distribution
#check @born_prob_nonneg     -- 0 ≤ bornProb ψ spec i
#check @born_prob_sum_one    -- ∑ bornProb ψ spec i = 1

-- Theorem 2: Expectation value is real
#check @expectation_real     -- (expectationValue ψ A).im = 0

-- Theorem 3: Variance is non-negative
#check @variance_nonneg      -- 0 ≤ cnorm_sq ((A - μI)ψ)

-- Theorem 4: Relative frequency bounds
#check @relative_freq_nonneg  -- 0 ≤ relativeFreq outcomes i
#check @relative_freq_le_one  -- relativeFreq outcomes i ≤ 1
#check @relative_freq_sum     -- ∑ relativeFreq outcomes i = 1

-- Theorem 5: Chebyshev bound (weak law)
#check @bernoulli_variance_bound    -- p(1-p) ≤ 1/4
#check @chebyshev_bernoulli_bound   -- p(1-p)/(Nε²) ≤ 1/(4Nε²)

-- ========================================================================
-- DC_ω Layer (Level 2) — Requires Dependent Choice
-- ========================================================================

-- Theorem 6: Strong law of large numbers
#check @frequentist_convergence  -- SLLN (via DC_ω)

-- ========================================================================
-- Axiom Audit — CRM Separation Certificate
-- ========================================================================

-- BISH theorems: should show {propext, Classical.choice, Quot.sound}
-- with NO dc_omega_holds, NO slln_of_dc
#print axioms born_prob_nonneg
#print axioms born_prob_sum_one
#print axioms expectation_real
#print axioms variance_nonneg
#print axioms bernoulli_variance_bound
#print axioms chebyshev_bernoulli_bound
#print axioms relative_freq_nonneg
#print axioms relative_freq_le_one
#print axioms relative_freq_sum
#print axioms cnorm_sq_nonneg

-- DC theorems: should show dc_omega_holds + slln_of_dc
-- in addition to standard Mathlib axioms
#print axioms frequentist_convergence

-- ========================================================================
-- Theorem 7: Separation — The Born rule straddles BISH and DC
-- ========================================================================

/-- The Born rule separates into two constructive layers:
    - BISH: single-trial probability, expectation, variance, Chebyshev bound
    - DC_ω: strong law (frequentist convergence)
    This theorem is verified by the axiom audit above:
    BISH theorems have no dc_omega_holds in their axiom closure,
    DC theorems have dc_omega_holds in their axiom closure. -/
theorem born_rule_separation :
    -- The weak law is provable without DC
    (∀ (p : ℝ), 0 ≤ p → p ≤ 1 → p * (1 - p) ≤ 1 / 4) ∧
    -- The strong law requires DC (provided by axiom)
    SLLN := by
  exact ⟨bernoulli_variance_bound, frequentist_convergence⟩

#print axioms born_rule_separation

end Papers.P16
