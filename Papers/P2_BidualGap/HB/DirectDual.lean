/-
Papers/P2_BidualGap/HB/DirectDual.lean
Direct construction: G : (c₀ →L ℝ) →L ℝ via G(f) = ∑ f(e n)
-/
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section
open Classical
open scoped BigOperators    -- brings ∑ notation
open Filter Finset Set

namespace Papers.P2.HB

/-- Our model for `c₀` on the discrete space `ℕ`. -/
abbrev c₀ := ZeroAtInftyContinuousMap ℕ ℝ

/-- The standard basis: `e n` is `1` at `n` and `0` elsewhere. -/
def e (n : ℕ) : c₀ :=
{ toContinuousMap :=
  { toFun := fun m => if m = n then (1 : ℝ) else 0
    -- ℕ is discrete ⇒ any function is continuous
    continuous_toFun := continuous_of_discreteTopology },
  zero_at_infty' :=
  by
    -- {n} is compact in a discrete space
    have hK : IsCompact ({n} : Set ℕ) := isCompact_singleton
    -- its complement is in the cocompact filter
    have hCompl : ({n} : Set ℕ)ᶜ ∈ cocompact ℕ := hK.compl_mem_cocompact
    -- rewrite {m | m ≠ n} as ({n})ᶜ
    have hSet : {m : ℕ | m ≠ n} = ({n} : Set ℕ)ᶜ := by
      ext m; by_cases hm : m = n <;> simp [hm]
    -- on that set the value is exactly 0, hence tends to 0
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    refine Filter.mem_of_superset (by simpa [hSet] using hCompl) ?_
    intro m hm
    have : m ≠ n := by
      -- turn membership in complement into inequality
      simpa [hSet] using hm
    simp [this, hε] }

/-- Coordinate evaluation `δ n`. -/
def δ (n : ℕ) : c₀ →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun x => (x : ℕ → ℝ) n
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
    1
    (by
      intro x
      -- |x n| ≤ ‖x‖ via the inclusion to BCF
      simpa using
        (BoundedContinuousFunction.norm_coe_le_norm (ZeroAtInftyContinuousMap.toBCF x) n)
    )

/-- Normalized coefficient for the sign vector. -/
def coeff (f : c₀ →L[ℝ] ℝ) (n : ℕ) : ℝ :=
  if h : f (e n) = 0 then 0 else (f (e n)) / ‖f (e n)‖

lemma abs_coeff_le_one (f : c₀ →L[ℝ] ℝ) (n : ℕ) : |coeff f n| ≤ 1 := by
  by_cases h : f (e n) = 0
  · simp [coeff, h]
  · have : ‖f (e n)‖ ≠ 0 := by simpa [Real.norm_eq_abs, h] using (norm_ne_zero_iff.mpr (by exact h))
    -- |(f/‖f‖)| = 1
    simp [coeff, h, this, Real.norm_eq_abs, abs_div, abs_of_pos (norm_pos_iff.mpr (by exact h))]

lemma coeff_mul_eval_abs (f : c₀ →L[ℝ] ℝ) (n : ℕ) :
    coeff f n * f (e n) = ‖f (e n)‖ := by
  unfold coeff
  split_ifs with h
  · simp [h]
  · -- We have coeff f n = f (e n) / ‖f (e n)‖
    -- So coeff f n * f (e n) = (f (e n) / ‖f (e n)‖) * f (e n) = f (e n) * f (e n) / ‖f (e n)‖
    -- We need to show this equals ‖f (e n)‖
    -- Since f (e n) ≠ 0, we have f (e n) ∈ ℝ \ {0}
    -- For real numbers: x * x = |x| * |x| = ‖x‖ * ‖x‖
    have : f (e n) * f (e n) = ‖f (e n)‖ * ‖f (e n)‖ := by
      simp only [Real.norm_eq_abs]
      exact (abs_mul_abs_self _).symm
    rw [div_mul_eq_mul_div, this, mul_div_cancel_left₀]
    exact norm_ne_zero_iff.mpr h

/-- Finite "sign vector": sum of basis with sign coefficients. -/
def signVector (f : c₀ →L[ℝ] ℝ) (F : Finset ℕ) : c₀ :=
  ∑ n ∈ F, (coeff f n) • e n

-- Helper: evaluate signVector at m
private lemma signVector_eval
  (f : c₀ →L[ℝ] ℝ) (F : Finset ℕ) (m : ℕ) :
  (signVector f F) m = (if m ∈ F then coeff f m else 0) := by
  classical
  -- δ m (x) is definitionally x m
  have hδ : (δ m) (signVector f F) = (signVector f F) m := rfl
  -- linearity through the finite sum
  have : (δ m) (signVector f F) =
      ∑ n ∈ F, coeff f n * (if n = m then (1 : ℝ) else 0) := by
    -- δ m (e n) = if n = m then 1 else 0
    simp [signVector, map_sum, map_smul, δ, e, eq_comm, mul_comm]
  -- reduce the finite sum
  by_cases hm : m ∈ F
  · have eq1 : ∑ n ∈ F, coeff f n * (if n = m then (1:ℝ) else 0) = coeff f m := by
      rw [Finset.sum_eq_single m]
      · simp
      · intro n hn hne
        simp [if_neg hne]
      · intro hmF
        exact absurd hm hmF
    rw [← hδ, this, eq1]
    simp [hm]
  · have eq1 : ∑ n ∈ F, coeff f n * (if n = m then (1:ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have : n ≠ m := by
        intro h; exact hm (h ▸ hn)
      simp [if_neg this]
    rw [← hδ, this, eq1]
    simp [hm]

lemma signVector_norm_le_one (f : c₀ →L[ℝ] ℝ) (F : Finset ℕ) :
    ‖signVector f F‖ ≤ 1 := by
  classical
  -- pointwise bound
  have hpt : ∀ m, |(signVector f F) m| ≤ 1 := by
    intro m
    by_cases hm : m ∈ F
    · -- value is coeff f m
      simpa [signVector_eval f F m, hm, Real.norm_eq_abs]
           using abs_coeff_le_one f m
    · -- value is 0
      simpa [signVector_eval f F m, hm]
  -- pass to the sup norm via BCF
  have : ‖ZeroAtInftyContinuousMap.toBCF (signVector f F)‖ ≤ 1 := by
    -- use the standard "pointwise ≤ r ⇒ ‖·‖ ≤ r"
    rw [BoundedContinuousFunction.norm_le (by norm_num : (0:ℝ) ≤ 1)]
    intro m
    simpa [Real.norm_eq_abs] using hpt m
  -- same norm on c₀
  exact this

/-- Key finite-sum bound: `∑_{n∈F} |f(e n)| ≤ ‖f‖`. -/
lemma finite_sum_bound (f : c₀ →L[ℝ] ℝ) (F : Finset ℕ) :
    ∑ n ∈ F, ‖f (e n)‖ ≤ ‖f‖ := by
  classical
  have hfx : f (signVector f F) = ∑ n ∈ F, ‖f (e n)‖ := by
    simp only [signVector]
    rw [map_sum]
    simp only [map_smul]
    have : ∑ n ∈ F, coeff f n • f (e n) = ∑ n ∈ F, ‖f (e n)‖ := by
      congr 1
      ext n
      exact coeff_mul_eval_abs f n
    exact this
  have h_nonneg : 0 ≤ f (signVector f F) := by
    rw [hfx]
    apply Finset.sum_nonneg
    intro n _
    exact norm_nonneg _
  calc ∑ n ∈ F, ‖f (e n)‖ = f (signVector f F) := hfx.symm
    _ = |f (signVector f F)| := by rw [abs_eq_self.mpr h_nonneg]
    _ ≤ ‖f‖ * ‖signVector f F‖ := by
      have := f.le_opNorm (signVector f F)
      simp only [Real.norm_eq_abs] at this
      exact this
    _ ≤ ‖f‖ * 1 := by
      have := signVector_norm_le_one f F
      exact mul_le_mul_of_nonneg_left this (norm_nonneg f)
    _ = ‖f‖ := by simp

/-- Absolute summability of `n ↦ f(e n)`. -/
lemma summable_abs_eval (f : c₀ →L[ℝ] ℝ) : Summable (fun n => ‖f (e n)‖) := by
  classical
  -- Use bounded partial sums to show summability
  have h_nonneg : 0 ≤ fun n => ‖f (e n)‖ := fun n => norm_nonneg _
  have h_bound : ∀ (s : Finset ℕ), ∑ n ∈ s, ‖f (e n)‖ ≤ ‖f‖ := finite_sum_bound f
  exact summable_of_sum_le h_nonneg h_bound

lemma summable_eval (f : c₀ →L[ℝ] ℝ) : Summable (fun n => f (e n)) :=
  Summable.of_norm (summable_abs_eval f)

/-- The bidual witness: `G(f) = ∑ f(e n)`. -/
noncomputable def G : (c₀ →L[ℝ] ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    {
      toFun := fun (f : c₀ →L[ℝ] ℝ) => ∑' (n : ℕ), f (e n),
      map_add' := fun (f g : c₀ →L[ℝ] ℝ) => by
        have hf := summable_eval f
        have hg := summable_eval g
        -- (f+g)(e n) = f(e n) + g(e n) by linearity
        have : ∀ n, (f + g) (e n) = f (e n) + g (e n) := fun n => by
          simp only [ContinuousLinearMap.add_apply]
        simp only [this]
        exact hf.tsum_add hg,
      map_smul' := fun (a : ℝ) (f : c₀ →L[ℝ] ℝ) => by
        have hf := summable_eval f
        -- (a•f)(e n) = a * f(e n)
        have : ∀ n, (a • f) (e n) = a * f (e n) := fun n => by
          simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
        simp only [this, tsum_mul_left]
        rfl
    }
    1
    (fun (f : c₀ →L[ℝ] ℝ) => by
      have hf_abs := summable_abs_eval f
      have h1 : ‖∑' n, f (e n)‖ ≤ ∑' n, ‖f (e n)‖ := by
        -- norm_tsum_le_tsum_norm requires Summable of norms
        exact norm_tsum_le_tsum_norm hf_abs
      -- Use a more basic bound
      have h2 : (∑' n, ‖f (e n)‖) ≤ ‖f‖ := by
        apply hf_abs.tsum_le_of_sum_le
        intro s
        exact finite_sum_bound f s
      calc ‖∑' n, f (e n)‖ ≤ ∑' n, ‖f (e n)‖ := h1
        _ ≤ ‖f‖ := h2
        _ = 1 * ‖f‖ := by simp
    )

/-- `G(δ m) = 1` for every `m`. -/
lemma G_delta (m : ℕ) : G (δ m) = 1 := by
  classical
  -- only `n = m` contributes
  have hsupp : {n : ℕ | (δ m) (e n) ≠ 0} ⊆ {m} := by
    intro n hn
    by_contra hnm
    have : (δ m) (e n) = 0 := by 
      simp [δ, e]
      intro h
      exact hnm h.symm
    exact hn this
  have hfin : Set.Finite {n : ℕ | (δ m) (e n) ≠ 0} :=
    Set.Finite.subset (Set.finite_singleton m) hsupp
  -- `tsum` over finite support reduces to a finite sum
  have : (∑' n, (δ m) (e n)) = ∑ n ∈ hfin.toFinset, (δ m) (e n) := 
    tsum_eq_sum (fun n hn => by simp at hn; exact hn)
  -- the finite set is {m}; compute the sum
  have hone : (δ m) (e m) = 1 := by simp [δ, e]
  have : (∑' n, (δ m) (e n)) = 1 := by
    rw [this]
    have : hfin.toFinset = {m} := by
      ext n
      simp [Set.Finite.mem_toFinset]
      constructor
      · intro h
        have : n ∈ {n : ℕ | (δ m) (e n) ≠ 0} := by simpa using h
        have : n ∈ {m} := hsupp this
        simpa using this
      · intro h
        simp at h
        rw [h]
        exact hone.symm ▸ one_ne_zero
    rw [this]
    simp [hone]
  simpa [G] using this

end Papers.P2.HB