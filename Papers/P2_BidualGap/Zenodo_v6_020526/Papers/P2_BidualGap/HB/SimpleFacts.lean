import Mathlib.Analysis.Normed.Group.ZeroAtInfty
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

noncomputable section
open Classical Filter Metric

lemma constOne_not_in_c0_image :
  BoundedContinuousFunction.const ℕ (1 : ℝ) ∉
    Set.range
      (ZeroAtInftyContinuousMap.toBCF :
        ZeroAtInftyContinuousMap ℕ ℝ → BoundedContinuousFunction ℕ ℝ) := by
  intro h
  rcases h with ⟨g, hg⟩
  -- g → 0 at infinity
  have tend0 : Tendsto (g : ℕ → ℝ) (cocompact ℕ) (nhds 0) := g.zero_at_infty'
  -- pointwise: g n = 1 for all n
  have h_one : ∀ n, g n = 1 := by
    intro n
    have := congrArg (fun F => F n) hg
    simp only [BoundedContinuousFunction.const_apply] at this
    exact this
  -- ε = 1/2 contradiction
  have : ∀ᶠ n in cocompact ℕ, dist (g n) 0 < (1/2) :=
    (Metric.tendsto_nhds.mp tend0) (1/2) (by norm_num)
  -- but dist (g n) 0 = ‖1‖ = 1
  have : ∀ᶠ _ in cocompact ℕ, (1 : ℝ) < 1/2 := by
    simpa [dist_eq_norm, h_one, norm_one] using this
  -- eventually false on a proper filter
  have h_mem : {n : ℕ | (1 : ℝ) < 1/2} ∈ cocompact ℕ := this
  have h_empty : {n : ℕ | (1 : ℝ) < 1/2} = (∅ : Set ℕ) := by
    ext n; simp; norm_num
  rw [h_empty] at h_mem
  have h_nebot : (cocompact ℕ).NeBot := inferInstance
  have h_bot : cocompact ℕ = ⊥ := Filter.empty_mem_iff_bot.mp h_mem
  exact absurd h_bot h_nebot.ne

lemma sep_from_constOne :
  ∀ f : ZeroAtInftyContinuousMap ℕ ℝ,
    (1/2 : ℝ) ≤ ‖f.toBCF - BoundedContinuousFunction.const ℕ (1 : ℝ)‖ := by
  intro f
  -- choose n with |f n| < 1/2 (from vanishing at ∞)
  have tend0 : Tendsto (f : ℕ → ℝ) (cocompact ℕ) (nhds 0) := f.zero_at_infty'
  have hε := (Metric.tendsto_nhds.mp tend0) (1/2) (by norm_num)
  -- pick any witness from the 'eventually' set
  classical
  have : {n : ℕ | dist (f n) 0 < 1/2}.Nonempty := by
    -- cocompact is a proper filter, so 'eventually' a nonempty set is nonempty
    have h_mem : {n : ℕ | dist (f n) 0 < 1/2} ∈ cocompact ℕ := hε
    -- if it were empty, the filter would contain ∅, contradiction
    have hne : (cocompact ℕ).NeBot := inferInstance
    by_contra hempty
    simp only [Set.not_nonempty_iff_eq_empty] at hempty
    rw [hempty] at h_mem
    have : cocompact ℕ = ⊥ := Filter.empty_mem_iff_bot.mp h_mem
    exact absurd this hne.ne
  rcases this with ⟨N, hN⟩
  have h_small : ‖(f : ℕ → ℝ) N‖ < 1/2 := by simpa [dist_zero_right] using hN
  -- pointwise lower bound at N
  have : (1/2 : ℝ) ≤ |(f : ℕ → ℝ) N - 1| := by
    have h1 : (1 : ℝ) - 1/2 ≤ |1| - ‖(f : ℕ → ℝ) N‖ := by
      have : ‖(f : ℕ → ℝ) N‖ ≤ (1/2) := le_of_lt h_small
      simp only [abs_one]
      linarith
    -- |f N - 1| ≥ |1| - |f N|
    have h2 : |1| - ‖(f : ℕ → ℝ) N‖ ≤ |1 - (f : ℕ → ℝ) N| := 
      abs_sub_abs_le_abs_sub 1 (f N)
    have h3 : |1 - (f : ℕ → ℝ) N| = |(f : ℕ → ℝ) N - 1| := abs_sub_comm _ _
    calc (1/2 : ℝ) = (1 : ℝ) - 1/2 := by norm_num
                 _ ≤ |1| - ‖(f : ℕ → ℝ) N‖ := h1
                 _ ≤ |1 - (f : ℕ → ℝ) N| := h2
                 _ = |(f : ℕ → ℝ) N - 1| := h3
  -- sup norm ≥ pointwise value
  have h_norm : (1/2 : ℝ) ≤ ‖(f.toBCF - BoundedContinuousFunction.const ℕ (1 : ℝ)) N‖ := by
    simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply,
               BoundedContinuousFunction.const_apply,
               Real.norm_eq_abs]
    exact this
  exact h_norm.trans (BoundedContinuousFunction.norm_coe_le_norm _ _)