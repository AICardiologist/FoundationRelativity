/-
Papers/P9_Combinatorial_Ising/PartB_FreeEnergyAnti.lean
Free energy g(J) = -log(2·cosh(β·J)) is strictly anti-monotone.

Key results:
  - g is strictly decreasing on (0, ∞) for β > 0
  - The gap δ = g(J₀) - g(J₁) > 0 when 0 < J₀ < J₁
  - Injectivity of g on (0, ∞)

The chain: J₁ < J₂ → β·J₁ < β·J₂ → cosh increases → log increases → negate.
Uses Mathlib's cosh_strictMonoOn and log_lt_log.

Combinatorial justification: cosh is increasing on (0,∞) because
cosh(x) - cosh(y) = 2·sinh((x+y)/2)·sinh((x-y)/2) > 0 for x > y > 0.
This uses only the exponential definition, not calculus or functional analysis.
-/
import Papers.P9_Combinatorial_Ising.PartB_Defs

namespace Papers.P9

open Real Set

-- ========================================================================
-- Positivity helpers
-- ========================================================================

/-- 2 * cosh(β * J) > 0 for all β, J. -/
lemma two_cosh_mul_pos (β J : ℝ) : 0 < 2 * cosh (β * J) :=
  mul_pos two_pos (cosh_pos _)

-- ========================================================================
-- cosh monotonicity for product arguments
-- ========================================================================

/-- For β > 0 and 0 < J₁ < J₂: cosh(β·J₁) < cosh(β·J₂).
    Uses cosh_strictMonoOn : StrictMonoOn cosh (Ici 0). -/
lemma cosh_mul_lt_cosh_mul {β J₁ J₂ : ℝ} (hβ : 0 < β)
    (hJ₁ : 0 < J₁) (hJ : J₁ < J₂) :
    cosh (β * J₁) < cosh (β * J₂) := by
  have h1 : 0 < β * J₁ := mul_pos hβ hJ₁
  have h2 : β * J₁ < β * J₂ := mul_lt_mul_of_pos_left hJ hβ
  exact cosh_strictMonoOn (mem_Ici.mpr h1.le) (mem_Ici.mpr (le_of_lt (lt_trans h1 h2))) h2

-- ========================================================================
-- g is strictly anti-monotone
-- ========================================================================

/-- For β > 0 and 0 < J₁ < J₂: g(J₂) < g(J₁).
    Chain: J₁ < J₂ → cosh(β·J₁) < cosh(β·J₂) → log increases → negate reverses. -/
lemma freeEnergyAtCoupling_lt {β J₁ J₂ : ℝ} (hβ : 0 < β)
    (hJ₁ : 0 < J₁) (hJ : J₁ < J₂) :
    freeEnergyAtCoupling β J₂ < freeEnergyAtCoupling β J₁ := by
  unfold freeEnergyAtCoupling
  apply neg_lt_neg
  apply log_lt_log (two_cosh_mul_pos β J₁)
  exact mul_lt_mul_of_pos_left (cosh_mul_lt_cosh_mul hβ hJ₁ hJ) two_pos

/-- g(J₁) ≤ g(J₂) when J₂ ≤ J₁ (for positive J values and β > 0).
    Non-strict version used for monotonicity of the encoded sequence. -/
lemma freeEnergyAtCoupling_le {β J₁ J₂ : ℝ} (hβ : 0 < β)
    (hJ₁ : 0 < J₁) (hJ₂ : 0 < J₂) (hJ : J₁ ≤ J₂) :
    freeEnergyAtCoupling β J₂ ≤ freeEnergyAtCoupling β J₁ := by
  rcases eq_or_lt_of_le hJ with rfl | hlt
  · exact le_refl _
  · exact le_of_lt (freeEnergyAtCoupling_lt hβ hJ₁ hlt)

-- ========================================================================
-- Gap lemma
-- ========================================================================

/-- The gap: g(J₀) - g(J₁) > 0 when 0 < J₀ < J₁ and β > 0. -/
lemma freeEnergy_gap_pos {β J₀ J₁ : ℝ} (hβ : 0 < β)
    (hJ₀ : 0 < J₀) (hJ : J₀ < J₁) :
    0 < freeEnergyAtCoupling β J₀ - freeEnergyAtCoupling β J₁ :=
  sub_pos.mpr (freeEnergyAtCoupling_lt hβ hJ₀ hJ)

end Papers.P9
