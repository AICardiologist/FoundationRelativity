/-
Papers/P2_BidualGap/HB/DirectDual.lean
Direct construction: G : (c₀ →L ℝ) →L ℝ via G(f) = ∑ f(e n)
-/
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Papers.P2_BidualGap.HB.SigmaEpsilon

noncomputable section
open scoped BigOperators    -- brings ∑ notation
open Filter Finset Set

namespace Papers.P2.HB
open sigma_eps

/-- Our model for `c₀` on the discrete space `ℕ`. -/
abbrev c₀ := ZeroAtInftyContinuousMap ℕ ℝ

/- Direct dual construction namespace to avoid name clashes. -/
namespace DirectDual

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

/-- Finite "approx sign vector": sum of basis with σ_ε coefficients. -/
def signVector (f : c₀ →L[ℝ] ℝ) (ε : ℝ) (F : Finset ℕ) : c₀ :=
  ∑ n ∈ F, (sigma_eps ε (f (e n))) • e n

-- Helper: evaluate signVector at m
private lemma signVector_eval
  (f : c₀ →L[ℝ] ℝ) (ε : ℝ) (F : Finset ℕ) (m : ℕ) :
  (signVector f ε F) m = (if m ∈ F then sigma_eps ε (f (e m)) else 0) := by
  -- δ m (x) is definitionally x m
  have hδ : (δ m) (signVector f ε F) = (signVector f ε F) m := rfl
  -- linearity through the finite sum
  have : (δ m) (signVector f ε F) =
      ∑ n ∈ F, sigma_eps ε (f (e n)) * (if n = m then (1 : ℝ) else 0) := by
    -- δ m (e n) = if n = m then 1 else 0
    simp [signVector, map_sum, map_smul, δ, e, eq_comm, mul_comm]
  -- reduce the finite sum
  by_cases hm : m ∈ F
  · have eq1 : ∑ n ∈ F, sigma_eps ε (f (e n)) * (if n = m then (1:ℝ) else 0)
        = sigma_eps ε (f (e m)) := by
      rw [Finset.sum_eq_single m]
      · simp
      · intro n hn hne
        simp [if_neg hne]
      · intro hmF
        exact absurd hm hmF
    rw [← hδ, this, eq1]
    simp [hm]
  · have eq1 : ∑ n ∈ F, sigma_eps ε (f (e n)) * (if n = m then (1:ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have : n ≠ m := by
        intro h; exact hm (h ▸ hn)
      simp [if_neg this]
    rw [← hδ, this, eq1]
    simp [hm]

lemma signVector_norm_le_one (f : c₀ →L[ℝ] ℝ) {ε : ℝ} (hε : 0 < ε) (F : Finset ℕ) :
    ‖signVector f ε F‖ ≤ 1 := by
  -- pointwise bound
  have hpt : ∀ m, |(signVector f ε F) m| ≤ 1 := by
    intro m
    by_cases hm : m ∈ F
    · -- value is sigma_eps
      have h := sigma_eps.abs_le_one (ε := ε) (t := f (e m)) hε
      simpa [signVector_eval f ε F m, hm] using h
    · -- value is 0
      simp [signVector_eval f ε F m, hm]
  -- pass to the sup norm via BCF
  have : ‖ZeroAtInftyContinuousMap.toBCF (signVector f ε F)‖ ≤ 1 := by
    -- use the standard "pointwise ≤ r ⇒ ‖·‖ ≤ r"
    rw [BoundedContinuousFunction.norm_le (by norm_num : (0:ℝ) ≤ 1)]
    intro m
    simpa [Real.norm_eq_abs] using hpt m
  -- same norm on c₀
  exact this

/-- Finite-sum bound with σ_ε: `∑ |f(e n)| ≤ ‖f‖ + ε |F|`. -/
lemma finite_sum_bound_eps (f : c₀ →L[ℝ] ℝ) {ε : ℝ} (hε : 0 < ε) (F : Finset ℕ) :
    ∑ n ∈ F, ‖f (e n)‖ ≤ ‖f‖ + ε * F.card := by
  -- lower bound from σ_ε
  have hlower :=
    (sigma_eps.finite_sum_lower_bound (hε) (s := F) (a := fun n => f (e n)))
  -- rewrite in terms of norms
  have hsum' :
      ∑ n ∈ F, ‖f (e n)‖
        ≤ (∑ n ∈ F, f (e n) * sigma_eps ε (f (e n))) + ε * F.card := by
    have h' : ∑ n ∈ F, |f (e n)| - ε * F.card
          ≤ ∑ n ∈ F, f (e n) * sigma_eps ε (f (e n)) := by
      simpa [Real.norm_eq_abs] using hlower
    -- move ε*card to the RHS
    exact (sub_le_iff_le_add).1 h'
  -- rewrite the sum via linearity
  have hsum :
      ∑ n ∈ F, f (e n) * sigma_eps ε (f (e n)) = f (signVector f ε F) := by
    simp [signVector, map_sum, map_smul, mul_comm]
  -- bound the evaluation by the op norm
  have hnorm : |f (signVector f ε F)| ≤ ‖f‖ * ‖signVector f ε F‖ := by
    have := f.le_opNorm (signVector f ε F)
    simpa [Real.norm_eq_abs] using this
  have hsign : ‖signVector f ε F‖ ≤ 1 := signVector_norm_le_one f hε F
  calc
    ∑ n ∈ F, ‖f (e n)‖
        ≤ f (signVector f ε F) + ε * F.card := by simpa [hsum] using hsum'
    _ ≤ |f (signVector f ε F)| + ε * F.card := by
        have := le_abs_self (f (signVector f ε F)); linarith
    _ ≤ (‖f‖ * ‖signVector f ε F‖) + ε * F.card := by
        exact add_le_add_right hnorm _
    _ ≤ ‖f‖ * 1 + ε * F.card := by
        exact add_le_add_right (mul_le_mul_of_nonneg_left hsign (norm_nonneg f)) _
    _ = ‖f‖ + ε * F.card := by ring

/-- Uniform bound: `∑_{n∈F} |f(e n)| ≤ 2‖f‖`. -/
lemma finite_sum_bound (f : c₀ →L[ℝ] ℝ) (F : Finset ℕ) :
    ∑ n ∈ F, ‖f (e n)‖ ≤ 2 * ‖f‖ := by
  by_cases hzero : ‖f‖ = 0
  · -- then f = 0, so all terms are 0
    have hf : f = 0 := by
      simpa using (ContinuousLinearMap.opNorm_zero_iff (f := f)).1 hzero
    subst hf
    have h0 : 0 ≤ (2:ℝ) * ‖(0 : c₀ →L[ℝ] ℝ)‖ := by
      exact mul_nonneg (by norm_num) (norm_nonneg (0 : c₀ →L[ℝ] ℝ))
    simpa using h0
  · -- take ε = ‖f‖ / (card + 1)
    have hpos : 0 < (F.card : ℝ) + 1 := by
      have : 0 ≤ (F.card : ℝ) := by exact_mod_cast (Nat.zero_le _)
      linarith
    set ε : ℝ := ‖f‖ / ((F.card : ℝ) + 1)
    have hε : 0 < ε := by
      have hnormpos : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg f) (Ne.symm hzero)
      exact div_pos hnormpos hpos
    have hbound := finite_sum_bound_eps f hε F
    -- show ε*card ≤ ‖f‖
    have hfrac : (F.card : ℝ) / ((F.card : ℝ) + 1) ≤ 1 := by
      have : (F.card : ℝ) ≤ (F.card : ℝ) + 1 := by linarith
      exact (div_le_one hpos).2 this
    have hεcard : ε * (F.card : ℝ) ≤ ‖f‖ := by
      -- ε * card = ‖f‖ * (card/(card+1))
      have hrewrite :
          ε * (F.card : ℝ) = ‖f‖ * ((F.card : ℝ) / ((F.card : ℝ) + 1)) := by
        simp [ε, div_mul_eq_mul_div, mul_div_assoc, mul_comm]
      -- use hfrac
      have h := mul_le_mul_of_nonneg_left hfrac (norm_nonneg f)
      simpa [hrewrite] using h
    -- conclude
    calc
      ∑ n ∈ F, ‖f (e n)‖ ≤ ‖f‖ + ε * F.card := hbound
      _ ≤ ‖f‖ + ‖f‖ := by
            have := hεcard
            linarith
      _ = 2 * ‖f‖ := by ring

/-- Absolute summability of `n ↦ f(e n)`. -/
lemma summable_abs_eval (f : c₀ →L[ℝ] ℝ) : Summable (fun n => ‖f (e n)‖) := by
  classical
  -- Use bounded partial sums to show summability
  have h_nonneg : 0 ≤ fun n => ‖f (e n)‖ := fun n => norm_nonneg _
  have h_bound : ∀ (s : Finset ℕ), ∑ n ∈ s, ‖f (e n)‖ ≤ 2 * ‖f‖ := finite_sum_bound f
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
    2
    (fun (f : c₀ →L[ℝ] ℝ) => by
      have hf_abs := summable_abs_eval f
      have h1 : ‖∑' n, f (e n)‖ ≤ ∑' n, ‖f (e n)‖ := by
        -- norm_tsum_le_tsum_norm requires Summable of norms
        exact norm_tsum_le_tsum_norm hf_abs
      -- Use a more basic bound
      have h2 : (∑' n, ‖f (e n)‖) ≤ 2 * ‖f‖ := by
        apply hf_abs.tsum_le_of_sum_le
        intro s
        exact finite_sum_bound f s
      calc ‖∑' n, f (e n)‖ ≤ ∑' n, ‖f (e n)‖ := h1
        _ ≤ 2 * ‖f‖ := h2
        _ = 2 * ‖f‖ := by simp
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

end DirectDual

end Papers.P2.HB
