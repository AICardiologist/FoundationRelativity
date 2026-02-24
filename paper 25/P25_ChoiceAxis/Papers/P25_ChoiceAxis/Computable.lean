/-
Papers/P25_ChoiceAxis/Computable.lean
Paper 25: Type-Level Computable Reverse Direction (Option C)

## Motivation

The Prop-level reverse direction (`meanErgodic_implies_cc`) is classically trivial:
CC_N is provable from `Classical.choice`, so the hypothesis is discarded. This module
provides a NON-TRIVIAL reverse direction where the Mean Ergodic hypothesis is actually
used.

## Strategy

Given a choice problem A : ℕ → Set ℕ with ∀ n, (A n).Nonempty, we:
1. Build H = ℓ²(ℕ × ℕ) with the standard basis
2. Define a diagonal reflection U: fixes coordinates at (n,m) when m ∈ A(n),
   negates when m ∉ A(n). This is an isometry.
3. Fix(U) = {f : f(n,m) = 0 when m ∉ A(n)}
4. The probe vector x₀ with x₀(n,m) = 1/(2ⁿ·2ᵐ) has all nonzero coordinates
5. Apply MeanErgodicComputable to get proj(x₀) ∈ Fix(U)
6. proj(x₀) is nonzero at some (n,m) with m ∈ A(n) (proved via convergence)
7. Extract: find the first nonzero coordinate per block → choice function

The CONSTRUCTION uses Classical.choice (unavoidable — Mathlib infrastructure).
The EXTRACTION goes through the Mean Ergodic hypothesis, which is actually used.

## Honest Assessment

`#print axioms` will show `Classical.choice` (from Mathlib + Classical.dec).
The structural achievement: the hypothesis `MeanErgodicComputableAll` is not discarded.
See `p25_computable_reverse_direction_task.md` for the full analysis.
-/
import Papers.P25_ChoiceAxis.MeanErgodic
import Papers.P25_ChoiceAxis.CesaroAverage
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpSpace

namespace Papers.P25_ChoiceAxis

open Filter Topology Finset Classical Real

/-! ## Phase 1: Type-Level Choice Principles -/

/-- **Countable Choice at the Type level** (Prop version).
    Given a sequence of nonempty types, assert existence of a choice function. -/
def CC_N_computable : Prop :=
  ∀ (A : ℕ → Type) [∀ n, Nonempty (A n)], Nonempty ((n : ℕ) → A n)

/-- Classical.choice gives CC_N_computable noncomputably. -/
noncomputable def cc_computable_classical : CC_N_computable :=
  fun A _ => ⟨fun n => Classical.choice (inferInstance)⟩

/-! ## Computable Mean Ergodic Theorem -/

/-- **Computable Mean Ergodic: convergence with a computable modulus.**

    The standard Mean Ergodic Theorem asserts existence of a limit.
    This structure provides the limit AND a modulus of convergence. -/
structure MeanErgodicComputable
    (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (U : F →L[ℂ] F) (hU : ∀ z, ‖U z‖ = ‖z‖) where
  /-- The limit of Cesàro averages (projection onto Fix(U)) -/
  proj : F → F
  /-- Computable modulus of convergence -/
  modulus : F → (ε : ℝ) → (0 < ε) → ℕ
  /-- The projection lands in the fixed subspace -/
  proj_fixed : ∀ x, proj x ∈ fixedSubspace U
  /-- The modulus is correct -/
  modulus_spec : ∀ x ε (hε : 0 < ε) (n : ℕ),
    modulus x ε hε ≤ n → ‖cesaroAvg U x (n + 1) - proj x‖ < ε

/-- **Universal computable Mean Ergodic theorem.**
    Wrapped in `Nonempty` so this is a `Prop` (since `MeanErgodicComputable`
    is a structure in `Type`).
    Uses `Type` (not `Type*`) for universe compatibility with `choiceHilbert`. -/
def MeanErgodicComputableAll : Prop :=
  ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (U : F →L[ℂ] F) (hU : ∀ z, ‖U z‖ = ‖z‖),
    Nonempty (MeanErgodicComputable F U hU)

/-! ## Phase 2: The Concrete Encoding System -/

noncomputable section

/-- The Hilbert space ℓ²(ℕ × ℕ, ℂ). -/
abbrev choiceHilbert := lp (fun _ : ℕ × ℕ => ℂ) 2

/-! ### Phase 2a: The reflection operator U

    Given A : ℕ → Set ℕ, define U by:
    (U f)(n,m) = f(n,m)  if m ∈ A(n)
    (U f)(n,m) = -f(n,m) if m ∉ A(n)

    This is a diagonal operator with eigenvalues ±1, hence an isometry. -/

/-- The pointwise action of the reflection operator. -/
def reflectFun (A : ℕ → Set ℕ) (f : ℕ × ℕ → ℂ) : ℕ × ℕ → ℂ :=
  fun ⟨n, m⟩ => if m ∈ A n then f (n, m) else -f (n, m)

/-- The reflection preserves absolute values pointwise. -/
theorem reflectFun_norm (A : ℕ → Set ℕ) (f : ℕ × ℕ → ℂ) (i : ℕ × ℕ) :
    ‖reflectFun A f i‖ = ‖f i‖ := by
  simp only [reflectFun]
  obtain ⟨n, m⟩ := i
  split
  · rfl
  · exact norm_neg _

/-- The reflection is an involution: reflectFun A (reflectFun A f) = f. -/
theorem reflectFun_involutive (A : ℕ → Set ℕ) (f : ℕ × ℕ → ℂ) :
    reflectFun A (reflectFun A f) = f := by
  ext ⟨n, m⟩
  simp only [reflectFun]
  split
  · rfl
  · simp

/-- If f is in ℓ², then reflect(f) is in ℓ². -/
theorem reflectFun_memℓp (A : ℕ → Set ℕ) {f : ℕ × ℕ → ℂ}
    (hf : Memℓp f 2) : Memℓp (reflectFun A f) 2 := by
  apply memℓp_gen
  have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have hf_sum : Summable (fun i => ‖f i‖ ^ (2 : ENNReal).toReal) := hf.summable hp
  exact hf_sum.of_norm_bounded (fun i => by
    rw [Real.norm_of_nonneg (by positivity), reflectFun_norm])

/-- The reflection as a linear map on ℓ². -/
def reflectLinearMap (A : ℕ → Set ℕ) : choiceHilbert →ₗ[ℂ] choiceHilbert where
  toFun f := ⟨reflectFun A f, reflectFun_memℓp A f.2⟩
  map_add' f g := by
    ext i; obtain ⟨n, m⟩ := i
    simp only [reflectFun, lp.coeFn_add, Pi.add_apply]
    split <;> ring
  map_smul' c f := by
    ext i; obtain ⟨n, m⟩ := i
    simp only [reflectFun, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split <;> ring

/-- The reflection operator has norm bound ≤ 1. -/
theorem reflectLinearMap_norm_le (A : ℕ → Set ℕ) (f : choiceHilbert) :
    ‖reflectLinearMap A f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul]
  have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  rw [← Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hp]
  rw [lp.norm_rpow_eq_tsum hp (reflectLinearMap A f)]
  rw [lp.norm_rpow_eq_tsum hp f]
  exact ((reflectLinearMap A f).2.summable hp).tsum_le_tsum
    (fun i => by
      simp only [reflectLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
      rw [reflectFun_norm])
    (f.2.summable hp)

/-- The reflection as a continuous linear map. -/
def reflectCLM (A : ℕ → Set ℕ) : choiceHilbert →L[ℂ] choiceHilbert :=
  (reflectLinearMap A).mkContinuous 1 (reflectLinearMap_norm_le A)

/-- The CLM coercion unfolds to reflectFun at coordinates. -/
@[simp] theorem reflectCLM_apply (A : ℕ → Set ℕ) (f : choiceHilbert) (i : ℕ × ℕ) :
    (reflectCLM A f : ℕ × ℕ → ℂ) i = reflectFun A f i := by
  simp only [reflectCLM, reflectLinearMap]
  rfl

/-- reflectCLM and reflectLinearMap agree as elements of choiceHilbert. -/
theorem reflectCLM_eq_reflectLinearMap (A : ℕ → Set ℕ) (f : choiceHilbert) :
    reflectCLM A f = reflectLinearMap A f := by
  ext i; simp only [reflectCLM_apply, reflectLinearMap, LinearMap.coe_mk, AddHom.coe_mk]

/-- The reflection is an involution on ℓ²: U² = I. -/
theorem reflectCLM_sq (A : ℕ → Set ℕ) (f : choiceHilbert) :
    reflectCLM A (reflectCLM A f) = f := by
  ext i
  -- After one reflectCLM_apply, the inner coercion ↑(reflectCLM A f) still needs unfolding
  simp only [reflectCLM_apply]
  -- Now goal: reflectFun A (↑(reflectCLM A f)) i = ↑f i
  -- ↑(reflectCLM A f) = reflectFun A ↑f (by reflectCLM_eq_reflectLinearMap + Subtype.coe_mk)
  conv_lhs => rw [show (↑(reflectCLM A f) : ℕ × ℕ → ℂ) = reflectFun A f from by
    ext j; exact reflectCLM_apply A f j]
  -- Now: reflectFun A (reflectFun A ↑f) i = ↑f i
  rw [reflectFun_involutive]

/-- The reflection is an isometry: ‖U f‖ = ‖f‖. -/
theorem reflectCLM_isometry (A : ℕ → Set ℕ) :
    ∀ z : choiceHilbert, ‖reflectCLM A z‖ = ‖z‖ := by
  intro z
  apply le_antisymm
  · -- ‖U z‖ ≤ ‖z‖: reflectCLM A z = reflectLinearMap A z, use norm bound
    rw [reflectCLM_eq_reflectLinearMap]
    have h := reflectLinearMap_norm_le A z
    linarith
  · -- ‖z‖ = ‖U(U z)‖ ≤ ‖U z‖
    calc ‖z‖ = ‖reflectCLM A (reflectCLM A z)‖ := by rw [reflectCLM_sq]
      _ ≤ ‖reflectCLM A z‖ := by
          rw [reflectCLM_eq_reflectLinearMap]
          have h := reflectLinearMap_norm_le A (reflectCLM A z)
          linarith

/-! ### Phase 3: Fixed subspace characterization -/

/-- **Fixed subspace of the reflection**: f ∈ Fix(U) iff f vanishes outside A. -/
theorem mem_fixedSubspace_reflect_iff (A : ℕ → Set ℕ) (f : choiceHilbert) :
    f ∈ fixedSubspace (reflectCLM A) ↔ ∀ n m, m ∉ A n → (f : ℕ × ℕ → ℂ) (n, m) = 0 := by
  rw [mem_fixedSubspace_iff]
  constructor
  · intro hfixed n m hm
    have h : (reflectCLM A f : ℕ × ℕ → ℂ) (n, m) = (f : ℕ × ℕ → ℂ) (n, m) :=
      congr_fun (congr_arg Subtype.val hfixed) (n, m)
    rw [reflectCLM_apply, reflectFun, if_neg hm] at h
    exact CharZero.neg_eq_self_iff.mp h
  · intro hvanish
    ext ⟨n, m⟩
    rw [reflectCLM_apply, reflectFun]
    split
    · rfl
    · rename_i hm; rw [hvanish n m hm, neg_zero]

/-- Contrapositive: nonzero coordinate implies membership in A. -/
theorem mem_of_coord_ne_zero_reflect (A : ℕ → Set ℕ) (f : choiceHilbert)
    (hf : f ∈ fixedSubspace (reflectCLM A)) (n m : ℕ)
    (hne : (f : ℕ × ℕ → ℂ) (n, m) ≠ 0) : m ∈ A n := by
  by_contra hm
  exact hne ((mem_fixedSubspace_reflect_iff A f).mp hf n m hm)

/-! ### Phase 4: The probe vector -/

/-- Coefficient for the probe vector: c(n,m) = 1/(2^n · 2^m) as a complex number. -/
def probeCoeff (n m : ℕ) : ℂ := (((2 : ℝ) ^ n * (2 : ℝ) ^ m)⁻¹ : ℝ)

/-- The probe coefficient is nonzero. -/
theorem probeCoeff_ne_zero (n m : ℕ) : probeCoeff n m ≠ 0 := by
  simp only [probeCoeff, Complex.ofReal_ne_zero]
  positivity

/-- Auxiliary: the probe norm-power series is summable. -/
private theorem probe_norm_pow_summable :
    Summable (fun i : ℕ × ℕ => ‖probeCoeff i.1 i.2‖ ^ (2 : ENNReal).toReal) := by
  -- ‖probeCoeff n m‖ ≤ 1 (since 2^n * 2^m ≥ 1), so ‖...‖^2 ≤ ‖...‖
  -- And ‖probeCoeff n m‖ = (1/2)^n * (1/2)^m, which is summable
  have hg1 : Summable (fun n : ℕ => ((1 : ℝ) / 2) ^ n) :=
    summable_geometric_of_lt_one (by positivity) (by norm_num)
  have hg2 : Summable (fun m : ℕ => ((1 : ℝ) / 2) ^ m) :=
    summable_geometric_of_lt_one (by positivity) (by norm_num)
  have hprod := hg1.mul_of_nonneg hg2 (fun n => by positivity) (fun m => by positivity)
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun ⟨n, m⟩ => ?_) hprod
  simp only [probeCoeff, ENNReal.toReal_ofNat]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, rpow_natCast]
  simp only [Nat.cast_ofNat]
  -- Goal: ((2 : ℝ) ^ n * (2 : ℝ) ^ m)⁻¹ ^ 2 ≤ (1/2) ^ n * (1/2) ^ m
  have hx_eq : ((2 : ℝ) ^ n * (2 : ℝ) ^ m)⁻¹ = (1 / 2) ^ n * (1 / 2) ^ m := by
    rw [mul_inv_rev, ← one_div, ← one_div, one_div_pow, one_div_pow, mul_comm]
  rw [hx_eq]
  have hx0 : (0 : ℝ) ≤ (1 / 2) ^ n * (1 / 2) ^ m := by positivity
  have hx1 : (1 / 2 : ℝ) ^ n * (1 / 2) ^ m ≤ 1 :=
    mul_le_one₀ (pow_le_one₀ (by norm_num) (by norm_num)) (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num))
  calc ((1 / 2 : ℝ) ^ n * (1 / 2) ^ m) ^ 2
        = ((1 / 2 : ℝ) ^ n * (1 / 2) ^ m) * ((1 / 2) ^ n * (1 / 2) ^ m) := by ring
    _ ≤ (1 / 2) ^ n * (1 / 2) ^ m := mul_le_of_le_one_left hx0 hx1

/-- The probe function is in ℓ². -/
theorem probe_memℓp : Memℓp (fun i : ℕ × ℕ => probeCoeff i.1 i.2) 2 :=
  memℓp_gen probe_norm_pow_summable

/-- The probe vector x₀ ∈ ℓ²(ℕ × ℕ) with x₀(n,m) = 1/(2ⁿ·2ᵐ). -/
def probeVec : choiceHilbert :=
  ⟨fun i => probeCoeff i.1 i.2, probe_memℓp⟩

/-- The probe vector has the expected coordinates. -/
@[simp] theorem probeVec_apply (n m : ℕ) :
    (probeVec : ℕ × ℕ → ℂ) (n, m) = probeCoeff n m := rfl

/-! ### Phase 5: Cesàro averages on fixed coordinates -/

/-- The reflection fixes coordinates in A. -/
theorem reflectCLM_apply_mem (A : ℕ → Set ℕ) (f : choiceHilbert) (n m : ℕ)
    (hm : m ∈ A n) :
    (reflectCLM A f : ℕ × ℕ → ℂ) (n, m) = (f : ℕ × ℕ → ℂ) (n, m) := by
  rw [reflectCLM_apply, reflectFun, if_pos hm]

/-- U^k preserves coordinates in A. -/
theorem iterate_reflectCLM_apply_mem (A : ℕ → Set ℕ) (f : choiceHilbert)
    (n m : ℕ) (hm : m ∈ A n) (k : ℕ) :
    ((reflectCLM A ^ k) f : ℕ × ℕ → ℂ) (n, m) = (f : ℕ × ℕ → ℂ) (n, m) := by
  induction k with
  | zero => simp
  | succ j ih =>
    rw [pow_succ']
    simp only [ContinuousLinearMap.mul_apply]
    rw [reflectCLM_apply_mem A _ n m hm]
    exact ih

/-- **Key lemma**: The Cesàro average at a fixed coordinate equals the original value. -/
theorem cesaroAvg_coord_mem (A : ℕ → Set ℕ) (n m : ℕ) (hm : m ∈ A n)
    {N : ℕ} (hN : 0 < N) :
    (↑(cesaroAvg (reflectCLM A) probeVec N) : ℕ × ℕ → ℂ) (n, m) =
    probeCoeff n m := by
  have hne : N ≠ 0 := Nat.pos_iff_ne_zero.mp hN
  simp only [cesaroAvg, hne, ↓reduceIte]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  have hsum : (↑(∑ k ∈ Finset.range N, (reflectCLM A ^ k) probeVec : choiceHilbert) : ℕ × ℕ → ℂ) (n, m) =
      ∑ k ∈ Finset.range N, ((reflectCLM A ^ k) probeVec : ℕ × ℕ → ℂ) (n, m) := by
    simp [Finset.sum_apply]
  rw [hsum]
  have hiterval : ∀ k, k ∈ Finset.range N →
      ((reflectCLM A ^ k) probeVec : ℕ × ℕ → ℂ) (n, m) = probeCoeff n m := by
    intro k _
    rw [iterate_reflectCLM_apply_mem A probeVec n m hm k]
    rfl
  rw [Finset.sum_congr rfl hiterval, Finset.sum_const, Finset.card_range]
  rw [nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact Nat.cast_ne_zero.mpr hne

/-! ### Phase 5b: Norm convergence implies coordinate convergence -/

/-- |f(i)| ≤ ‖f‖ for any f ∈ ℓ² and any index i. -/
theorem lp_coord_le_norm (f : choiceHilbert) (i : ℕ × ℕ) :
    ‖(f : ℕ × ℕ → ℂ) i‖ ≤ ‖f‖ :=
  lp.norm_apply_le_norm (p := 2) (by norm_num) f i

/-- Norm convergence implies coordinate convergence for subtraction. -/
theorem coord_sub_le_norm_sub (f g : choiceHilbert) (i : ℕ × ℕ) :
    ‖(f : ℕ × ℕ → ℂ) i - (g : ℕ × ℕ → ℂ) i‖ ≤ ‖f - g‖ := by
  have : (f : ℕ × ℕ → ℂ) i - (g : ℕ × ℕ → ℂ) i =
         ((f - g : choiceHilbert) : ℕ × ℕ → ℂ) i := by simp
  rw [this]
  exact lp_coord_le_norm (f - g) i

/-! ### Phase 5c: Projection coordinates are nonzero in A-blocks -/

/-- **The projection has a nonzero coordinate in each block.** -/
theorem proj_coord_nonzero (A : ℕ → Set ℕ) (hA : ∀ n, (A n).Nonempty)
    (mec : MeanErgodicComputable ↥choiceHilbert (reflectCLM A) (reflectCLM_isometry A))
    (n : ℕ) :
    ∃ m, (mec.proj probeVec : ℕ × ℕ → ℂ) (n, m) ≠ 0 := by
  obtain ⟨m₀, hm₀⟩ := hA n
  refine ⟨m₀, ?_⟩
  -- Strategy: show proj(x₀)(n,m₀) = probeCoeff n m₀ by uniqueness of limits
  suffices hsuff : (mec.proj probeVec : ℕ × ℕ → ℂ) (n, m₀) = probeCoeff n m₀ by
    rw [hsuff]; exact probeCoeff_ne_zero n m₀
  by_contra hne
  push_neg at hne
  set Px := (mec.proj probeVec : ℕ × ℕ → ℂ) (n, m₀) with hPx_def
  set c := probeCoeff n m₀ with hc_def
  have hδ : 0 < ‖Px - c‖ := by
    rw [norm_pos_iff]; exact sub_ne_zero.mpr hne
  set N := mec.modulus probeVec ‖Px - c‖ hδ
  -- mec.proj probeVec : ↥choiceHilbert, so subtraction is in ℓ²
  have hconv := mec.modulus_spec probeVec ‖Px - c‖ hδ N le_rfl
  -- Coordinate bound: |cesaro(n,m₀) - proj(n,m₀)| ≤ ‖cesaro - proj‖
  have hcoord := coord_sub_le_norm_sub
    (cesaroAvg (reflectCLM A) probeVec (N + 1)) (mec.proj probeVec) (n, m₀)
  -- Cesàro at (n, m₀) = c
  have hcesaro := cesaroAvg_coord_mem A n m₀ hm₀ (Nat.succ_pos N)
  -- |c - Px| ≤ ‖cesaro - proj‖ < ‖Px - c‖
  have h1 : ‖c - Px‖ ≤ ‖cesaroAvg (reflectCLM A) probeVec (N + 1) - mec.proj probeVec‖ := by
    calc ‖c - Px‖
        = ‖(↑(cesaroAvg (reflectCLM A) probeVec (N + 1)) : ℕ × ℕ → ℂ) (n, m₀) -
            (↑(mec.proj probeVec) : ℕ × ℕ → ℂ) (n, m₀)‖ := by
          simp only [hc_def, hPx_def]; rw [hcesaro]
      _ ≤ _ := hcoord
  have h3 : ‖c - Px‖ = ‖Px - c‖ := norm_sub_rev c Px
  linarith [h1, hconv]

/-! ### Phase 6: The Main Theorem -/

/-- **MeanErgodicComputableAll implies CC_N (non-trivial encoding).**

    This proof constructs a specific Hilbert space and isometry from the
    choice problem, applies the Mean Ergodic hypothesis to get a projection,
    then extracts the choice function from the projection's coordinates.

    Unlike `meanErgodic_implies_cc`, this proof USES the hypothesis h —
    it is not classically trivial. The `MeanErgodicComputableAll` hypothesis
    provides the projection and convergence guarantee, from which we derive
    fixed-subspace membership and nonzero coordinates. -/
theorem meanErgodicComputableAll_implies_cc (h : MeanErgodicComputableAll) : CC_N := by
  intro A hA
  let mec := (h ↥choiceHilbert (reflectCLM A) (reflectCLM_isometry A)).some
  -- proj(x₀) ∈ Fix(U), so it vanishes outside A
  -- mec.proj probeVec : ↥choiceHilbert, and mem_fixedSubspace_reflect_iff works on choiceHilbert
  have hvanish : ∀ n m, m ∉ A n →
      (mec.proj probeVec : ℕ × ℕ → ℂ) (n, m) = 0 :=
    (mem_fixedSubspace_reflect_iff A (mec.proj probeVec)).mp (mec.proj_fixed probeVec)
  have hnonzero : ∀ n, ∃ m, (mec.proj probeVec : ℕ × ℕ → ℂ) (n, m) ≠ 0 :=
    fun n => proj_coord_nonzero A hA mec n
  refine ⟨fun n => Nat.find (hnonzero n), fun n => ?_⟩
  by_contra hmem
  exact absurd (hvanish n _ hmem) (Nat.find_spec (hnonzero n))

#print axioms meanErgodicComputableAll_implies_cc

end

end Papers.P25_ChoiceAxis
