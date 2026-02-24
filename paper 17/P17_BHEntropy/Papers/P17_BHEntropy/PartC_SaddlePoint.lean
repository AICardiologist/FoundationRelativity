/-
Papers/P17_BHEntropy/PartC_SaddlePoint.lean
Part C Tier 2: Saddle point existence and uniqueness.

Main result:
  ∃! t* > 0, Z(t*) = 1

The existence follows from the intermediate value theorem applied to Z
on an interval [a, b] where Z(a) > 1 > Z(b). The uniqueness follows
from strict anti-monotonicity.

THIS IS THE FIRST AXIOM READOUT POINT.
The IVT for continuous functions is provable in classical mathematics
via Mathlib's `intermediate_value_Icc`. The question is whether
Classical.choice enters through the IVT or through continuity of Z.

The `#print axioms` at the bottom reveals the answer.
-/
import Papers.P17_BHEntropy.PartC_GenFunc

noncomputable section
namespace Papers.P17

open Real Filter Set

-- ========================================================================
-- Continuity of Z
-- ========================================================================

/-- Z_term is continuous in t for each k. -/
lemma Z_term_continuous (k : ℕ) : Continuous (fun t : ℝ => Z_term t k) := by
  unfold Z_term
  fun_prop

/-- **Z is continuous on (0, ∞).**
    Axiomatized: requires showing locally uniform convergence of the
    partial sums on (0, ∞), which follows from the geometric comparison
    but needs careful application of Mathlib's `tendstoLocallyUniformlyOn`. -/
axiom Z_continuous_on : ContinuousOn Z (Ioi 0)

-- ========================================================================
-- Saddle point existence
-- ========================================================================

/-- There exist points a, b > 0 with Z(a) > 1 and Z(b) < 1.
    This follows from Z → ∞ at 0+ and Z → 0 at ∞. Axiomatized
    as the combination of the limit axioms with concrete witnesses. -/
axiom Z_crosses_one :
  ∃ (a b : ℝ), 0 < a ∧ a < b ∧ 1 < Z a ∧ Z b < 1

/-- **Saddle point exists: ∃ t* > 0, Z(t*) = 1 (Theorem 5.1).**

    Proof: Z is continuous on (0,∞), Z(a) > 1 > Z(b) for some
    0 < a < b, so by the intermediate value theorem there exists
    t* ∈ [a, b] with Z(t*) = 1.

    The uniqueness follows from strict anti-monotonicity of Z. -/
theorem saddle_point_exists :
    ∃ t_star : ℝ, 0 < t_star ∧ Z t_star = 1 := by
  obtain ⟨a, b, ha, hab, hZa, hZb⟩ := Z_crosses_one
  have hb : 0 < b := lt_trans ha hab
  -- Z is continuous on [a, b] ⊆ (0, ∞)
  have hcont : ContinuousOn Z (Icc a b) := by
    apply Z_continuous_on.mono
    intro x hx
    exact lt_of_lt_of_le ha hx.1
  -- IVT: ∃ t ∈ [a, b], Z(t) = 1 (using Icc' since Z is decreasing)
  have h1_mem : (1 : ℝ) ∈ Set.Icc (Z b) (Z a) :=
    ⟨le_of_lt hZb, le_of_lt hZa⟩
  obtain ⟨t_star, ht_mem, ht_val⟩ :=
    intermediate_value_Icc' (le_of_lt hab) hcont h1_mem
  exact ⟨t_star, lt_of_lt_of_le ha ht_mem.1, ht_val⟩

/-- **Saddle point is unique (Corollary of Theorem 5.1).**

    If Z(t₁) = Z(t₂) = 1 with t₁, t₂ > 0, then t₁ = t₂
    by strict anti-monotonicity. -/
theorem saddle_point_unique (t₁ t₂ : ℝ) (h₁ : 0 < t₁) (h₂ : 0 < t₂)
    (hZ₁ : Z t₁ = 1) (hZ₂ : Z t₂ = 1) : t₁ = t₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := Z_strictAntiOn h₁ h₂ h
    linarith
  · have := Z_strictAntiOn h₂ h₁ h
    linarith

-- ========================================================================
-- Axiom readout (Tier 2 checkpoint)
-- ========================================================================

-- THE KEY DISCOVERY: what axioms does the saddle point existence need?
#print axioms saddle_point_exists
#print axioms saddle_point_unique

end Papers.P17
end
