/-
Papers/P25_ChoiceAxis/CesaroAverage.lean
Paper 25: Cesàro Averages for Bounded Linear Operators

Defines Cesàro averages of iterates of a bounded linear operator on a
Hilbert space and establishes their basic properties:

  1. cesaroAvg_of_fixed: averages of fixed points are the fixed point
  2. cesaroAvg_range_tendsto_zero: averages on Range(U - I) tend to 0
  3. cesaroAvg_norm_le: uniform bound by ‖x‖ when U is an isometry

These results are pure analysis — no choice principles needed.
They form the technical backbone of the mean ergodic theorem proof.
-/
import Papers.P25_ChoiceAxis.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic

namespace Papers.P25_ChoiceAxis

open Finset Filter Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## Cesàro Average Definition -/

/-- Cesàro average of the first n iterates of a continuous linear map U
    applied to x: A_n(x) = (1/n) ∑_{k=0}^{n-1} U^k x.

    For n = 0, returns 0 (degenerate case). -/
noncomputable def cesaroAvg (U : E →L[ℂ] E) (x : E) (n : ℕ) : E :=
  if n = 0 then 0
  else (n : ℂ)⁻¹ • (∑ k ∈ Finset.range n, (U ^ k) x)

/-! ## Fixed Subspace -/

/-- The fixed subspace Fix(U) = {x : U x = x} = ker(U - id).
    As a closed submodule of a Hilbert space. -/
def fixedSubspace (U : E →L[ℂ] E) : Submodule ℂ E :=
  LinearMap.ker (U.toLinearMap - LinearMap.id)

theorem mem_fixedSubspace_iff (U : E →L[ℂ] E) (x : E) :
    x ∈ fixedSubspace U ↔ U x = x := by
  simp [fixedSubspace, LinearMap.mem_ker, sub_eq_zero]

/-! ## Basic Properties -/

/-- If U x = x, then U^k x = x for all k. -/
theorem iterate_of_fixed (U : E →L[ℂ] E) (x : E) (hx : U x = x) (k : ℕ) :
    (U ^ k) x = x := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ContinuousLinearMap.mul_apply, hx, ih]

/-- **Cesàro averages of fixed points equal the fixed point.**
    If x ∈ Fix(U), then A_n(x) = x for all n ≥ 1. -/
theorem cesaroAvg_of_fixed (U : E →L[ℂ] E) (x : E)
    (hx : x ∈ fixedSubspace U) {n : ℕ} (hn : 0 < n) :
    cesaroAvg U x n = x := by
  rw [mem_fixedSubspace_iff] at hx
  have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  simp only [cesaroAvg, hne, ↓reduceIte]
  have : ∑ k ∈ Finset.range n, (U ^ k) x = ∑ _k ∈ Finset.range n, x := by
    apply Finset.sum_congr rfl; intro k _; exact iterate_of_fixed U x hx k
  rw [this, Finset.sum_const, Finset.card_range]
  -- Goal: (↑n)⁻¹ • n • x = x  (where n • is ℕ-nsmul)
  have hne' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hne
  -- Convert: m • y = (↑m : ℂ) • y  for a module over ℂ
  suffices h : ∀ (m : ℕ) (y : E), m • y = (m : ℂ) • y from by
    rw [h, smul_smul, inv_mul_cancel₀ hne', one_smul]
  intro m y
  induction m with
  | zero => simp
  | succ k ih => rw [succ_nsmul, ih, Nat.cast_succ, add_smul, one_smul]

/-- **Telescoping for Range(U - I).**
    For x = U y - y, the sum ∑_{k=0}^{n-1} U^k x telescopes to U^n y - y. -/
theorem sum_iterate_sub (U : E →L[ℂ] E) (y : E) (n : ℕ) :
    ∑ k ∈ Finset.range n, (U ^ k) (U y - y) = (U ^ n) y - y := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, map_sub]
    rw [pow_succ, ContinuousLinearMap.mul_apply]
    abel

/-- **Cesàro averages on Range(U - I): norm bound.**
    If x = U y - y, then ‖A_n(x)‖ ≤ 2‖y‖/n.

    This uses the telescoping identity and does not require any choice. -/
theorem cesaroAvg_range_norm_le (U : E →L[ℂ] E) (y : E) {n : ℕ} (hn : 0 < n)
    (hU : ∀ z, ‖U z‖ = ‖z‖) :
    ‖cesaroAvg U (U y - y) n‖ ≤ 2 * ‖y‖ / n := by
  have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  simp only [cesaroAvg, hne, ↓reduceIte]
  rw [sum_iterate_sub, norm_smul, norm_inv, Complex.norm_natCast]
  -- ‖U^n y - y‖ ≤ ‖U^n y‖ + ‖y‖ = 2‖y‖
  have hUnorm : ∀ m, ‖(U ^ m) y‖ = ‖y‖ := by
    intro m; induction m with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, hU, ih]
  have hbound : ‖(U ^ n) y - y‖ ≤ 2 * ‖y‖ := by
    calc ‖(U ^ n) y - y‖ ≤ ‖(U ^ n) y‖ + ‖y‖ := norm_sub_le _ _
    _ = ‖y‖ + ‖y‖ := by rw [hUnorm n]
    _ = 2 * ‖y‖ := by ring
  calc (↑n : ℝ)⁻¹ * ‖(U ^ n) y - y‖
      ≤ (↑n : ℝ)⁻¹ * (2 * ‖y‖) := by
        apply mul_le_mul_of_nonneg_left hbound
        positivity
    _ = 2 * ‖y‖ / ↑n := by ring

/-- **Cesàro averages on Range(U - I) converge to zero.**
    Convergence version of the norm bound. -/
theorem cesaroAvg_range_tendsto_zero (U : E →L[ℂ] E) (y : E)
    (hU : ∀ z, ‖U z‖ = ‖z‖) :
    Tendsto (fun n => cesaroAvg U (U y - y) (n + 1)) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- We need N such that 2‖y‖/(n+1) < ε for n ≥ N
  -- Sufficient: n+1 > 2‖y‖/ε, i.e., n ≥ ⌈2‖y‖/ε⌉
  refine ⟨⌈2 * ‖y‖ / ε⌉₊, fun n hn => ?_⟩
  rw [dist_zero_right]
  have hn1 : (0 : ℕ) < n + 1 := Nat.succ_pos n
  calc ‖cesaroAvg U (U y - y) (n + 1)‖
      ≤ 2 * ‖y‖ / (↑(n + 1) : ℝ) := cesaroAvg_range_norm_le U y hn1 hU
    _ < ε := by
        by_cases hy : ‖y‖ = 0
        · simp [hy]; exact hε
        · rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ↑(n + 1))]
          have h1 : 2 * ‖y‖ / ε ≤ ↑⌈2 * ‖y‖ / ε⌉₊ := Nat.le_ceil _
          have h2 : (⌈2 * ‖y‖ / ε⌉₊ : ℝ) ≤ ↑n := by exact_mod_cast hn
          have h3 : (↑n : ℝ) < ↑(n + 1) := by exact_mod_cast Nat.lt_succ_iff.mpr le_rfl
          calc 2 * ‖y‖ = (2 * ‖y‖ / ε) * ε := by field_simp
            _ ≤ ↑⌈2 * ‖y‖ / ε⌉₊ * ε := by apply mul_le_mul_of_nonneg_right h1 (le_of_lt hε)
            _ ≤ ↑n * ε := by apply mul_le_mul_of_nonneg_right h2 (le_of_lt hε)
            _ < ↑(n + 1) * ε := by apply mul_lt_mul_of_pos_right h3 hε
            _ = ε * ↑(n + 1) := by ring

/-- **Uniform bound on Cesàro averages for isometries.**
    If U is an isometry, then ‖A_n(x)‖ ≤ ‖x‖ for all n ≥ 1. -/
theorem cesaroAvg_norm_le (U : E →L[ℂ] E) (hU : ∀ z, ‖U z‖ = ‖z‖)
    (x : E) {n : ℕ} (hn : 0 < n) :
    ‖cesaroAvg U x n‖ ≤ ‖x‖ := by
  have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  simp only [cesaroAvg, hne, ↓reduceIte]
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  have hiter : ∀ k, ‖(U ^ k) x‖ = ‖x‖ := by
    intro k; induction k with
    | zero => simp
    | succ m ih => rw [pow_succ', ContinuousLinearMap.mul_apply, hU, ih]
  have hsum : ‖∑ k ∈ Finset.range n, (U ^ k) x‖ ≤ n * ‖x‖ := by
    calc ‖∑ k ∈ Finset.range n, (U ^ k) x‖
        ≤ ∑ k ∈ Finset.range n, ‖(U ^ k) x‖ := norm_sum_le _ _
      _ = ∑ _k ∈ Finset.range n, ‖x‖ := by
          apply Finset.sum_congr rfl; intro k _; exact hiter k
      _ = n * ‖x‖ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc (↑n : ℝ)⁻¹ * ‖∑ k ∈ Finset.range n, (U ^ k) x‖
      ≤ (↑n : ℝ)⁻¹ * (↑n * ‖x‖) := by
        apply mul_le_mul_of_nonneg_left hsum; positivity
    _ = ‖x‖ := by
        rw [← mul_assoc, inv_mul_cancel₀, one_mul]
        exact_mod_cast hne

end

end Papers.P25_ChoiceAxis
