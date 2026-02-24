/-
  Paper 30: The Physical Dispensability of the Fan Theorem
  ApproxAttain.lean — LPO implies approximate EVT

  Main theorems:
    - approxEVT_of_lpo: LPO → ApproxEVT
    - approxEVT_of_exactEVT: ExactEVT → ApproxEVT
    - empirical_completeness: LPO → for any ε > 0, sup is ε-attainable

  The first theorem composes bmc_of_lpo with sup_exists_of_bmc.
  The second is trivial: if f attains its max at x*, take x_ε = x*.
-/
import Papers.P30_FTDispensability.SupExists

noncomputable section
namespace Papers.P30

open Set

-- ========================================================================
-- LPO → ApproxEVT
-- ========================================================================

/-- LPO implies the approximate extreme value theorem.
    Composition: LPO → BMC → sup exists + ε-attainment. -/
theorem approxEVT_of_lpo (hlpo : LPO) : ApproxEVT := by
  intro f a b hab hf
  exact sup_exists_of_bmc (bmc_of_lpo hlpo) f a b hab hf

-- ========================================================================
-- ExactEVT → ApproxEVT
-- ========================================================================

/-- Exact EVT trivially implies approximate EVT.
    If f attains its max at x*, then S = f(x*) works and x_ε = x* for all ε. -/
theorem approxEVT_of_exactEVT (hexact : ExactEVT) : ApproxEVT := by
  intro f a b hab hf
  obtain ⟨x, hx_mem, hx_max⟩ := hexact f a b hab hf
  exact ⟨f x, hx_max, fun ε hε => ⟨x, hx_mem, by linarith⟩⟩

-- ========================================================================
-- Empirical completeness
-- ========================================================================

/-- Empirical completeness: under LPO, for any ε > 0, there exists
    x ∈ [a,b] such that f(y) < f(x) + ε for all y ∈ [a,b].
    This is the "no experiment can tell" formulation. -/
theorem empirical_completeness (hlpo : LPO)
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ x ∈ Icc a b, ∀ y ∈ Icc a b, f y < f x + ε := by
  obtain ⟨S, hS_ub, hS_approx⟩ := approxEVT_of_lpo hlpo f a b hab hf
  obtain ⟨x, hx_mem, hx_close⟩ := hS_approx ε hε
  exact ⟨x, hx_mem, fun y hy => by linarith [hS_ub y hy]⟩

end Papers.P30
end
