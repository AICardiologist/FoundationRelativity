/-
  Paper 22: Markov's Principle and the Constructive Cost of Eventual Decay
  Defs/EncodedRate.lean — Binary encoding of decay rate

  Given α : ℕ → Bool, define:
    λ_α = Σₙ (if α(n) then (1/2)^(n+1) else 0)

  Key properties:
    - λ_α ≥ 0, summable, bounded by 1
    - λ_α = 0 ⟺ ∀ n, α(n) = false
    - If α(k) = true, then (1/2)^(k+1) ≤ λ_α
    - Partial sum + tail bound for witness extraction
-/
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Basic

namespace Papers.P22

noncomputable section

-- ========================================================================
-- Term definitions and basic properties
-- ========================================================================

/-- The term of the encoded rate series. -/
def encodedRateTerm (α : ℕ → Bool) (n : ℕ) : ℝ :=
  if α n then ((1 : ℝ) / 2) ^ (n + 1) else 0

/-- Each term of the encoded rate is non-negative. -/
theorem encodedRateTerm_nonneg (α : ℕ → Bool) (n : ℕ) :
    0 ≤ encodedRateTerm α n := by
  unfold encodedRateTerm
  split
  · apply pow_nonneg; norm_num
  · exact le_refl 0

/-- Each term is bounded by the geometric series (1/2)^(n+1). -/
theorem encodedRateTerm_le (α : ℕ → Bool) (n : ℕ) :
    encodedRateTerm α n ≤ ((1 : ℝ) / 2) ^ (n + 1) := by
  unfold encodedRateTerm
  split
  · exact le_refl _
  · apply pow_nonneg; norm_num

-- ========================================================================
-- Summability
-- ========================================================================

/-- The geometric series (1/2)^(n+1) is summable. -/
theorem summable_half_pow_succ :
    Summable (fun n : ℕ => ((1 : ℝ) / 2) ^ (n + 1)) := by
  have h := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
  simp_rw [pow_succ]
  exact h.mul_right _

/-- The encoded rate series is summable. -/
theorem encodedRate_summable (α : ℕ → Bool) :
    Summable (encodedRateTerm α) :=
  Summable.of_nonneg_of_le (encodedRateTerm_nonneg α) (encodedRateTerm_le α) summable_half_pow_succ

-- ========================================================================
-- Encoded rate and basic properties
-- ========================================================================

/-- The encoded decay rate: λ_α = Σₙ (if α(n) then (1/2)^(n+1) else 0). -/
def encodedRate (α : ℕ → Bool) : ℝ :=
  ∑' n, encodedRateTerm α n

/-- The encoded rate is non-negative. -/
theorem encodedRate_nonneg (α : ℕ → Bool) : 0 ≤ encodedRate α :=
  tsum_nonneg (encodedRateTerm_nonneg α)

-- ========================================================================
-- Zero-iff characterization
-- ========================================================================

/-- If all terms are false, the encoded rate is zero. -/
theorem encodedRate_eq_zero_of_all_false (α : ℕ → Bool)
    (hall : ∀ n, α n = false) : encodedRate α = 0 := by
  unfold encodedRate
  have : encodedRateTerm α = fun _ => 0 := by
    ext n; unfold encodedRateTerm; simp [hall n]
  rw [this, tsum_zero]

/-- If the encoded rate is zero, all terms are false. -/
theorem all_false_of_encodedRate_eq_zero (α : ℕ → Bool)
    (hzero : encodedRate α = 0) : ∀ n, α n = false := by
  intro n
  by_contra hne
  push_neg at hne
  have htrue : α n = true := by
    cases h : α n
    · exact absurd h hne
    · rfl
  have hterm_pos : 0 < encodedRateTerm α n := by
    unfold encodedRateTerm; rw [if_pos htrue]
    apply pow_pos; norm_num
  have hsum_pos : 0 < encodedRate α := by
    unfold encodedRate
    exact (encodedRate_summable α).tsum_pos (encodedRateTerm_nonneg α) n hterm_pos
  linarith

/-- The encoded rate is zero iff all entries are false. -/
theorem encodedRate_eq_zero_iff (α : ℕ → Bool) :
    encodedRate α = 0 ↔ ∀ n, α n = false :=
  ⟨all_false_of_encodedRate_eq_zero α, encodedRate_eq_zero_of_all_false α⟩

-- ========================================================================
-- Partial sums and tail bound
-- ========================================================================

/-- Partial sum of the encoded rate up to index k. -/
def partialRate (α : ℕ → Bool) (k : ℕ) : ℝ :=
  (Finset.range (k + 1)).sum (encodedRateTerm α)

/-- Each term in the partial sum is non-negative (for Finset API). -/
theorem encodedRateTerm_nonneg' (α : ℕ → Bool) :
    ∀ n ∈ Finset.range (k + 1), 0 ≤ encodedRateTerm α n :=
  fun n _hn => encodedRateTerm_nonneg α n

/-- Partial sum is at most the full tsum. -/
theorem partialRate_le_encodedRate (α : ℕ → Bool) (k : ℕ) :
    partialRate α k ≤ encodedRate α := by
  unfold partialRate encodedRate
  exact (encodedRate_summable α).sum_le_tsum (Finset.range (k + 1))
    (fun n _hn => encodedRateTerm_nonneg α n)

/-- The encoded rate is bounded above by 1.
    encodedRate α ≤ Σ (1/2)^(n+1) = 1. -/
theorem encodedRate_le_one (α : ℕ → Bool) : encodedRate α ≤ 1 := by
  unfold encodedRate
  calc ∑' n, encodedRateTerm α n
      ≤ ∑' n, ((1 : ℝ) / 2) ^ (n + 1) :=
        (encodedRate_summable α).tsum_le_tsum (fun n => encodedRateTerm_le α n)
          summable_half_pow_succ
    _ = ((1 : ℝ) / 2) * ∑' n, ((1 : ℝ) / 2) ^ n := by
        simp_rw [pow_succ']; rw [tsum_mul_left]
    _ = ((1 : ℝ) / 2) * (1 - (1 : ℝ) / 2)⁻¹ := by
        congr 1; exact tsum_geometric_of_lt_one (by norm_num) (by norm_num)
    _ = 1 := by norm_num

set_option maxHeartbeats 400000 in
/-- The tail bound: encodedRate α - partialRate α k ≤ (1/2)^(k+1). -/
theorem encodedRate_sub_partialRate_le (α : ℕ → Bool) (k : ℕ) :
    encodedRate α - partialRate α k ≤ ((1 : ℝ) / 2) ^ (k + 1) := by
  suffices h : encodedRate α ≤ partialRate α k + ((1 : ℝ) / 2) ^ (k + 1) by linarith
  -- Decompose tsum = partial + tail
  have hdecomp := (encodedRate_summable α).sum_add_tsum_nat_add (k + 1)
  unfold encodedRate partialRate
  rw [← hdecomp]
  gcongr
  -- Need: tail ≤ (1/2)^(k+1)
  -- tail = Σ_{n≥0} encodedRateTerm α (n + k + 1) ≤ Σ_{n≥0} (1/2)^(k+1) · (1/2)^(n+1)
  --      = (1/2)^(k+1) · Σ (1/2)^(n+1) = (1/2)^(k+1) · 1
  have hs_tail := (summable_nat_add_iff (k + 1)).mpr (encodedRate_summable α)
  have hbound : ∀ n, encodedRateTerm α (n + (k + 1)) ≤
      ((1 : ℝ) / 2) ^ (k + 1) * ((1 : ℝ) / 2) ^ (n + 1) := by
    intro n
    calc encodedRateTerm α (n + (k + 1))
        ≤ ((1 : ℝ) / 2) ^ (n + (k + 1) + 1) := encodedRateTerm_le α _
      _ = ((1 : ℝ) / 2) ^ (k + 1) * ((1 : ℝ) / 2) ^ (n + 1) := by
          rw [← pow_add]; congr 1; omega
  have hs_geom : Summable (fun n => ((1 : ℝ) / 2) ^ (k + 1) * ((1 : ℝ) / 2) ^ (n + 1)) :=
    summable_half_pow_succ.mul_left _
  -- Σ (1/2)^(n+1) = 1 (proved once for reuse)
  have hgeom_sum : ∑' n, ((1 : ℝ) / 2) ^ (n + 1) = 1 := by
    simp_rw [pow_succ']
    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  calc ∑' n, encodedRateTerm α (n + (k + 1))
      ≤ ∑' n, (((1 : ℝ) / 2) ^ (k + 1) * ((1 : ℝ) / 2) ^ (n + 1)) :=
        hs_tail.tsum_le_tsum hbound hs_geom
    _ = ((1 : ℝ) / 2) ^ (k + 1) * ∑' n, ((1 : ℝ) / 2) ^ (n + 1) := tsum_mul_left
    _ = ((1 : ℝ) / 2) ^ (k + 1) * 1 := by rw [hgeom_sum]
    _ = ((1 : ℝ) / 2) ^ (k + 1) := mul_one _

-- ========================================================================
-- Witness extraction from positive partial sum
-- ========================================================================

/-- If the partial sum is positive, there exists a witness. -/
theorem witness_from_partial_sum_pos (α : ℕ → Bool) (k : ℕ)
    (hpos : 0 < partialRate α k) :
    ∃ n, α n = true := by
  unfold partialRate at hpos
  have ⟨n, _hn_mem, hn_pos⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun i _hi => encodedRateTerm_nonneg α i)).mp hpos
  have hαn : α n = true := by
    by_contra h
    have : encodedRateTerm α n = 0 := by
      unfold encodedRateTerm
      simp only [ite_eq_right_iff]
      intro htrue; exact absurd htrue h
    linarith
  exact ⟨n, hαn⟩

end

end Papers.P22
