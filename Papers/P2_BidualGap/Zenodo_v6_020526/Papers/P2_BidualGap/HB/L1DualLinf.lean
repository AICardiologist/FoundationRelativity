/- 
  Papers/P2_BidualGap/HB/L1DualLinf.lean
  ℓ¹ dual coefficients and op-norm formula (for ℕ-indexed sequences).
  This file avoids the large DualIsometriesComplete import and is tailored
  to the WLPO→DualIsBanach path.
-/
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Instances.ENNReal.Lemmas

noncomputable section

namespace Papers.P2.HB

open scoped BigOperators

-- ℓ¹ and ℓ^∞ on ℕ with real scalars
abbrev l1 : Type := lp (fun _ : ℕ => ℝ) 1
abbrev linf : Type := lp (fun _ : ℕ => ℝ) ⊤

/-- The ℓ¹ basis vector at `n`. -/
noncomputable def l1basis (n : ℕ) : l1 := lp.single 1 n (1 : ℝ)

@[simp] lemma l1basis_apply_self (n : ℕ) : (l1basis n : ℕ → ℝ) n = 1 := by
  simp [l1basis]

@[simp] lemma l1basis_apply_ne {n m : ℕ} (h : m ≠ n) : (l1basis n : ℕ → ℝ) m = 0 := by
  simp [l1basis, h]

lemma l1basis_norm (n : ℕ) : ‖l1basis n‖ = 1 := by
  -- use `lp.norm_single` at p = 1
  have hp : (0 : ENNReal) < 1 := by simpa using (zero_lt_one : (0 : ENNReal) < 1)
  simpa [l1basis] using (lp.norm_single (p := (1 : ENNReal)) (i := n) (x := (1 : ℝ)) hp)

/-- Coefficients of a functional on ℓ¹. -/
noncomputable def coeffL1 (φ : l1 →L[ℝ] ℝ) : ℕ → ℝ :=
  fun n => φ (l1basis n)

/-- The bounded sequence of coefficients as an element of ℓ^∞. -/
noncomputable def coeffLinf (φ : l1 →L[ℝ] ℝ) : linf := by
  refine ⟨coeffL1 φ, ?_⟩
  -- bounded by ‖φ‖
  refine (memℓp_infty_iff : _).2 ?_
  refine ⟨‖φ‖, ?_⟩
  intro r hr
  rcases hr with ⟨n, rfl⟩
  -- |φ(e_n)| ≤ ‖φ‖
  have h := φ.le_opNorm (l1basis n)
  -- simplify using ‖e_n‖ = 1
  simpa [coeffL1, l1basis_norm, mul_one, Real.norm_eq_abs] using h

@[simp] lemma coeffLinf_apply (φ : l1 →L[ℝ] ℝ) (n : ℕ) :
    (coeffLinf φ : ℕ → ℝ) n = φ (l1basis n) := by
  rfl

/-- ℓ¹ norm formula (p = 1). -/
lemma l1_norm_eq_tsum (x : l1) : ‖x‖ = ∑' n : ℕ, ‖x n‖ := by
  -- use `lp.norm_rpow_eq_tsum` with p = 1
  have hp : 0 < (1 : ENNReal).toReal := by
    simp
  have h := lp.norm_rpow_eq_tsum (p := (1 : ENNReal)) hp x
  -- rpow with exponent 1 is identity
  simp [Real.rpow_one] at h
  exact h

/-- Expansion of `φ x` as a series of coefficients. -/
lemma phi_hasSum_coeff (φ : l1 →L[ℝ] ℝ) (x : l1) :
    HasSum (fun n : ℕ => x n * coeffL1 φ n) (φ x) := by
  -- `x` is the sum of its basis vectors
  have hx : HasSum (fun n : ℕ => lp.single (1 : ENNReal) n (x n)) x := by
    -- use lp.hasSum_single (p ≠ ∞)
    haveI : Fact (1 ≤ (1 : ENNReal)) := ⟨by simp⟩
    simpa using (lp.hasSum_single (p := (1 : ENNReal)) (hp := by simp) x)
  -- map through φ
  have hx' : HasSum (fun n : ℕ => φ (lp.single (1 : ENNReal) n (x n))) (φ x) :=
    (ContinuousLinearMap.hasSum (φ := φ) hx)
  -- rewrite termwise
  refine HasSum.congr_fun hx' ?_
  intro n
  -- `lp.single 1 n (x n)` is `x n • l1basis n`
  have hsingle :
      lp.single (1 : ENNReal) n (x n) = (x n) • l1basis n := by
    ext m
    by_cases hm : m = n
    · subst hm
      simp [l1basis, lp.single_apply_self, smul_eq_mul]
    · simp [l1basis, lp.single_apply_ne, hm, smul_eq_mul]
  -- rewrite via linearity
  -- note: `HasSum.congr_fun` expects `g n = f n`
  calc
    x n * coeffL1 φ n = x n * φ (l1basis n) := by rfl
    _ = φ ((x n) • l1basis n) := by simp [smul_eq_mul]
    _ = φ (lp.single (1 : ENNReal) n (x n)) := by simpa [hsingle]

/-- Bound the op-norm by the ℓ^∞ norm of the coefficient sequence. -/
lemma opNorm_le_coeffLinf_norm (φ : l1 →L[ℝ] ℝ) :
    ‖φ‖ ≤ ‖coeffLinf φ‖ := by
  -- show that for any x, |φ x| ≤ ‖coeff‖∞ * ‖x‖₁
  refine ContinuousLinearMap.opNorm_le_bound (f := φ) (M := ‖coeffLinf φ‖) (by exact norm_nonneg _) ?_
  intro x
  -- series representation
  have hsum := phi_hasSum_coeff φ x
  -- compare each term with ‖coeff‖∞ * ‖x n‖
  have hle : ∀ n : ℕ, ‖x n * coeffL1 φ n‖ ≤ ‖coeffLinf φ‖ * ‖x n‖ := by
    intro n
    -- |x_n * b_n| ≤ ‖b‖∞ * |x_n|
    have hb : ‖coeffL1 φ n‖ ≤ ‖coeffLinf φ‖ := by
      -- norm_apply_le_norm for lp ∞
      have h := lp.norm_apply_le_norm (p := (⊤ : ENNReal)) (by simp) (coeffLinf φ) n
      simpa [coeffL1, coeffLinf_apply] using h
    -- use `‖x n * b n‖ = ‖x n‖ * ‖b n‖` in ℝ
    have hxnonneg : 0 ≤ ‖x n‖ := norm_nonneg _
    calc
      ‖x n * coeffL1 φ n‖ = ‖x n‖ * ‖coeffL1 φ n‖ := by
        simpa [Real.norm_eq_abs, abs_mul] using (norm_mul (x n) (coeffL1 φ n))
      _ ≤ ‖x n‖ * ‖coeffLinf φ‖ := by
        exact mul_le_mul_of_nonneg_left hb hxnonneg
      _ = ‖coeffLinf φ‖ * ‖x n‖ := by ring
  -- summability of comparison series
  have hsumx : Summable (fun n : ℕ => ‖x n‖) := by
    -- from membership in ℓ¹
    have hp : 0 < (1 : ENNReal).toReal := by simp
    simpa [Real.rpow_one] using (lp.hasSum_norm (p := (1 : ENNReal)) hp x).summable
  have hsumx' : Summable (fun n : ℕ => ‖coeffLinf φ‖ * ‖x n‖) :=
    (hsumx.mul_left ‖coeffLinf φ‖)
  have hsum'': Summable (fun n : ℕ => ‖x n * coeffL1 φ n‖) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => hle n) hsumx'
  -- bound |φ x| by sum of absolute values
  have hnorm : ‖φ x‖ ≤ ∑' n : ℕ, ‖x n * coeffL1 φ n‖ := by
    have htsum : (∑' n : ℕ, x n * coeffL1 φ n) = φ x := hsum.tsum_eq
    -- use absolute convergence bound
    simpa [Real.norm_eq_abs, htsum] using (norm_tsum_le_tsum_norm hsum'')
  -- compare sums
  have hsum_le : (∑' n : ℕ, ‖x n * coeffL1 φ n‖) ≤ ‖coeffLinf φ‖ * (∑' n : ℕ, ‖x n‖) := by
    have := (Summable.tsum_le_tsum (fun n => hle n) hsum'' hsumx')
    -- rewrite RHS
    simpa [tsum_mul_left] using this
  -- finish
  calc
    ‖φ x‖ ≤ ∑' n : ℕ, ‖x n * coeffL1 φ n‖ := hnorm
    _ ≤ ‖coeffLinf φ‖ * (∑' n : ℕ, ‖x n‖) := hsum_le
    _ = ‖coeffLinf φ‖ * ‖x‖ := by
      simp [l1_norm_eq_tsum]

/-- Reverse inequality via evaluation on basis vectors. -/
lemma coeffLinf_norm_le_opNorm (φ : l1 →L[ℝ] ℝ) :
    ‖coeffLinf φ‖ ≤ ‖φ‖ := by
  -- use `‖coeff‖∞ = ⨆ n, ‖coeff n‖` and each coeff bounded by ‖φ‖
  have hcoeff : ∀ n : ℕ, ‖coeffLinf φ n‖ ≤ ‖φ‖ := by
    intro n
    have h := φ.le_opNorm (l1basis n)
    simpa [coeffLinf_apply, coeffL1, l1basis_norm, mul_one, Real.norm_eq_abs] using h
  have hsup : (⨆ n : ℕ, ‖coeffLinf φ n‖) ≤ ‖φ‖ := by
    refine ciSup_le ?_
    intro n
    exact hcoeff n
  -- rewrite `‖coeffLinf φ‖` as the `ciSup`
  simpa [lp.norm_eq_ciSup] using hsup

/-- Op-norm equals ℓ^∞ norm of coefficients. -/
lemma opNorm_eq_coeffLinf_norm (φ : l1 →L[ℝ] ℝ) :
    ‖φ‖ = ‖coeffLinf φ‖ := by
  apply le_antisymm
  · exact opNorm_le_coeffLinf_norm φ
  · exact coeffLinf_norm_le_opNorm φ

end Papers.P2.HB
