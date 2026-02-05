-- Papers/P2_BidualGap/HB/SigmaEpsilon.lean
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Papers.P2.HB

/-- Constructive "approximate sign": `σ_ε(t) := t / (|t| + ε)`. -/
noncomputable def sigma_eps (ε : ℝ) (t : ℝ) : ℝ := t / (|t| + ε)

namespace sigma_eps

variable {ε t : ℝ}

@[simp] lemma zero (ε : ℝ) : sigma_eps ε 0 = 0 := by
  simp [sigma_eps]

/-- Denominator positivity used everywhere. -/
lemma denom_pos (hε : 0 < ε) (t : ℝ) : 0 < |t| + ε :=
  add_pos_of_nonneg_of_pos (abs_nonneg t) hε

/-- Uniform bound `|σ_ε(t)| ≤ 1` for `ε>0`. -/
lemma abs_le_one (hε : 0 < ε) (t : ℝ) : |sigma_eps ε t| ≤ 1 := by
  have hpos : 0 < |t| + ε := denom_pos (t:=t) hε
  have hfrac : |t| / (|t| + ε) ≤ 1 := by
    -- For `c>0`, `a/c ≤ 1 ↔ a ≤ c`
    have : |t| ≤ |t| + ε := by linarith
    simpa [div_le_one hpos] using this
  simpa [sigma_eps, abs_div, abs_of_pos hpos] using hfrac

/-- Convenient identity: `t * σ_ε(t) = t^2 / (|t| + ε)`. -/
lemma self_mul (t : ℝ) :
    t * sigma_eps ε t = (t * t) / (|t| + ε) := by
  simp [sigma_eps, mul_div_assoc]

/-- Key inequality (fully constructive): `t * σ_ε(t) ≥ |t| - ε` for `ε > 0`. -/
lemma t_mul_sigma_ge (hε : 0 < ε) (t : ℝ) :
    t * sigma_eps ε t ≥ |t| - ε := by
  -- Rewrite LHS using self_mul
  have hpos : 0 < |t| + ε := denom_pos (t:=t) hε
  rw [self_mul]
  -- Use t^2 = |t|^2
  have t_sq : t * t = |t|^2 := by
    simp [pow_two]
  rw [t_sq]
  -- Prove: |t|^2 / (|t| + ε) ≥ |t| - ε
  -- This is equivalent to: |t|^2 ≥ (|t| - ε) * (|t| + ε)
  -- Since (|t| - ε)(|t| + ε) = |t|^2 - ε^2 ≤ |t|^2
  have hdiff : (|t| - ε) * (|t| + ε) ≤ |t|^2 := by
    calc (|t| - ε) * (|t| + ε) 
      = |t|^2 - ε^2 := by ring
      _ ≤ |t|^2 := by
        have : 0 ≤ ε^2 := sq_nonneg ε
        linarith
  -- Divide both sides by |t| + ε > 0
  have := div_le_div_of_nonneg_right hdiff (le_of_lt hpos)
  -- Simplify LHS
  have hlhs : ((|t| - ε) * (|t| + ε)) / (|t| + ε) = |t| - ε := by
    field_simp [hpos.ne']
  rwa [hlhs] at this

/-- Finite-sum lower bound:
    `∑_{i∈s} a i * σ_ε(a i) ≥ ∑_{i∈s} |a i| - ε |s|`. -/
lemma finite_sum_lower_bound (hε : 0 < ε)
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    ∑ i ∈ s, a i * sigma_eps ε (a i)
      ≥ ∑ i ∈ s, |a i| - ε * s.card := by
  have hpt : ∀ i ∈ s, a i * sigma_eps ε (a i) ≥ |a i| - ε := by
    intro i _; exact t_mul_sigma_ge hε (a i)
  calc
    ∑ i ∈ s, a i * sigma_eps ε (a i)
        ≥ ∑ i ∈ s, (|a i| - ε) := Finset.sum_le_sum (fun i hi => hpt i hi)
    _ = (∑ i ∈ s, |a i|) - (∑ i ∈ s, ε) := by
          simp [Finset.sum_sub_distrib]
    _ = (∑ i ∈ s, |a i|) - ε * s.card := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

end sigma_eps
end Papers.P2.HB
