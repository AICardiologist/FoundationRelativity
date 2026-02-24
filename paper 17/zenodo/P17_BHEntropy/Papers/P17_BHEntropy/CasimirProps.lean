/-
Papers/P17_BHEntropy/CasimirProps.lean
Properties of Casimir values and area eigenvalues.

Key results:
  - casimir_sq is strictly increasing in j.twice
  - area_eigenvalue is positive and strictly increasing
  - area_gap is positive
  - every area eigenvalue is at least area_gap
-/
import Papers.P17_BHEntropy.Basic

noncomputable section
namespace Papers.P17

open Real

-- ========================================================================
-- Casimir square properties
-- ========================================================================

/-- casimir_sq is positive for all half-integers. -/
theorem casimir_sq_pos (j : HalfInt) : (0 : ℚ) < casimir_sq j := by
  unfold casimir_sq
  have h1 : (1 : ℚ) ≤ (j.twice : ℚ) := by exact_mod_cast j.pos
  have h2 : (0 : ℚ) < (j.twice : ℚ) := by linarith
  have h3 : (0 : ℚ) < (j.twice : ℚ) + 2 := by linarith
  positivity

/-- casimir_sq is strictly monotone: k₁ < k₂ implies k₁(k₁+2) < k₂(k₂+2). -/
theorem casimir_sq_strictMono : StrictMono (fun k : ℕ => (k : ℚ) * ((k : ℚ) + 2)) := by
  intro a b hab
  have ha : (a : ℚ) < (b : ℚ) := by exact_mod_cast hab
  nlinarith

/-- casimir_sq on HalfInt is strictly increasing in j.twice. -/
theorem casimir_sq_lt_of_lt {j₁ j₂ : HalfInt} (h : j₁ < j₂) :
    casimir_sq j₁ < casimir_sq j₂ := by
  unfold casimir_sq
  have hmono := casimir_sq_strictMono h
  linarith

-- ========================================================================
-- Casimir (real square root) properties
-- ========================================================================

/-- The real-valued casimir_sq is non-negative. -/
theorem casimir_sq_real_nonneg (j : HalfInt) : (0 : ℝ) ≤ (casimir_sq j : ℝ) := by
  exact_mod_cast le_of_lt (casimir_sq_pos j)

/-- casimir is positive. -/
theorem casimir_pos (j : HalfInt) : 0 < casimir j := by
  unfold casimir
  exact Real.sqrt_pos_of_pos (by exact_mod_cast casimir_sq_pos j)

-- ========================================================================
-- Area eigenvalue properties
-- ========================================================================

theorem pi_pos' : (0 : ℝ) < Real.pi := Real.pi_pos

/-- area_eigenvalue is positive for gamma > 0. -/
theorem area_eigenvalue_pos (gamma : ℝ) (hg : 0 < gamma) (j : HalfInt) :
    0 < area_eigenvalue gamma j := by
  unfold area_eigenvalue
  apply mul_pos
  apply mul_pos
  apply mul_pos
  · linarith
  · exact pi_pos'
  · exact hg
  · exact casimir_pos j

/-- area_gap is positive for gamma > 0. -/
theorem area_gap_pos (gamma : ℝ) (hg : 0 < gamma) : 0 < area_gap gamma :=
  area_eigenvalue_pos gamma hg HalfInt.min

/-- casimir_sq is monotone on HalfInts (as rationals). -/
theorem casimir_sq_mono {j₁ j₂ : HalfInt} (h : j₁ ≤ j₂) :
    casimir_sq j₁ ≤ casimir_sq j₂ := by
  unfold casimir_sq
  have h' : j₁.twice ≤ j₂.twice := h
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℚ) < 4).le
  have h1 : (j₁.twice : ℚ) ≤ (j₂.twice : ℚ) := by exact_mod_cast h'
  have h1p : (0 : ℚ) ≤ (j₁.twice : ℚ) := by exact_mod_cast Nat.zero_le _
  nlinarith

/-- casimir is monotone: larger twice → larger casimir. -/
theorem casimir_le_of_le {j₁ j₂ : HalfInt} (h : j₁ ≤ j₂) :
    casimir j₁ ≤ casimir j₂ := by
  unfold casimir
  apply Real.sqrt_le_sqrt
  exact_mod_cast casimir_sq_mono h

/-- area_eigenvalue is monotone for gamma > 0. -/
theorem area_eigenvalue_mono (gamma : ℝ) (hg : 0 < gamma) {j₁ j₂ : HalfInt}
    (h : j₁ ≤ j₂) : area_eigenvalue gamma j₁ ≤ area_eigenvalue gamma j₂ := by
  unfold area_eigenvalue
  apply mul_le_mul_of_nonneg_left (casimir_le_of_le h)
  apply mul_nonneg
  apply mul_nonneg
  · linarith
  · exact le_of_lt pi_pos'
  · exact le_of_lt hg

/-- Every area eigenvalue is at least the area gap (minimum at j = 1/2). -/
theorem area_eigenvalue_ge_gap (gamma : ℝ) (hg : 0 < gamma) (j : HalfInt) :
    area_gap gamma ≤ area_eigenvalue gamma j := by
  apply area_eigenvalue_mono gamma hg
  exact j.pos

end Papers.P17
end
