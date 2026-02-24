/-
  Paper 30: The Physical Dispensability of the Fan Theorem
  Main.lean — Master theorem + axiom audit

  Assembles the main results:
    1. LPO → ApproxEVT (approximate extreme value theorem)
    2. ExactEVT ↔ FanTheorem (exact attainment requires FT)
    3. Empirical completeness (LPO suffices for all finite-precision predictions)
    4. Variational stratification (EL is BISH, approx min is LPO, exact min is FT)

  Axiom budget:
    - bmc_of_lpo: Bridges–Vîță 2006, Theorem 2.1.5
    - el_unique_bish: Paper 28 (BISH, equation-solving content)
    - minimizer_iff_ft_cited: Paper 28 (minimizer ↔ FT)
-/
import Papers.P30_FTDispensability.ApproxAttain
import Papers.P30_FTDispensability.Separation
import Papers.P30_FTDispensability.Variational

noncomputable section
namespace Papers.P30

open Set

-- ========================================================================
-- Master theorem: Physical dispensability of the Fan Theorem
-- ========================================================================

/-- The Fan Theorem is physically dispensable.

    This theorem assembles the three pillars of Paper 30:
    (1) LPO → ApproxEVT: approximate optimization needs only LPO ≡ BMC
    (2) ExactEVT ↔ FT: exact attainment is equivalent to the Fan Theorem
    (3) Empirical completeness: for any ε > 0, LPO provides an ε-optimal point

    Since no finite-precision experiment can distinguish exact from ε-approximate
    optimization, the Fan Theorem is dispensable for all empirical predictions. -/
theorem ft_physically_dispensable :
    -- Pillar 1: LPO suffices for approximate optimization
    (LPO → ApproxEVT) ∧
    -- Pillar 2: Exact optimization is equivalent to FT
    (ExactEVT ↔ FanTheorem) ∧
    -- Pillar 3: LPO provides empirical completeness
    (LPO → ∀ (f : ℝ → ℝ) (a b : ℝ), a < b → ContinuousOn f (Icc a b) →
      ∀ ε : ℝ, 0 < ε →
        ∃ x ∈ Icc a b, ∀ y ∈ Icc a b, f y < f x + ε) :=
  ⟨approxEVT_of_lpo, exactEVT_iff_ft, empirical_completeness⟩

-- ========================================================================
-- Axiom audit
-- ========================================================================

-- Core result: LPO → ApproxEVT
-- Expected: [propext, Classical.choice, Quot.sound, bmc_of_lpo]
#print axioms approxEVT_of_lpo

-- Separation: ExactEVT ↔ FT
-- Expected: [propext, Classical.choice, Quot.sound]
-- (no custom axioms — pure rescaling argument)
#print axioms exactEVT_iff_ft

-- Empirical completeness
-- Expected: [propext, Classical.choice, Quot.sound, bmc_of_lpo]
#print axioms empirical_completeness

-- Variational stratification
-- Expected: [propext, Classical.choice, Quot.sound, bmc_of_lpo,
--            el_unique_bish, minimizer_iff_ft_cited]
#print axioms variational_stratification

-- Master theorem
-- Expected: [propext, Classical.choice, Quot.sound, bmc_of_lpo]
#print axioms ft_physically_dispensable

end Papers.P30
end
