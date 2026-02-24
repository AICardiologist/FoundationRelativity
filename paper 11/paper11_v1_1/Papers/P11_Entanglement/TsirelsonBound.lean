/-
Papers/P11_Entanglement/TsirelsonBound.lean
Paper 11: Constructive Cost of Quantum Entanglement — CRM over Mathlib.

The Tsirelson bound: for the CHSH operator C on ℂ² ⊗ ℂ²,
‖C *ᵥ ψ‖² ≤ 8 for any unit vector ψ.

Formulated algebraically:
  re(star(C *ᵥ ψ) ⬝ᵥ (C *ᵥ ψ)) ≤ 8  when star ψ ⬝ᵥ ψ = 1.

The proof factors into:
  1. C = A⊗(B+B') + A'⊗(B−B')           (chsh_decomp)
  2. star(A⊗P·v)⬝ᵥ(A⊗P·v) = star(I⊗P·v)⬝ᵥ(I⊗P·v) (involution_tensor)
  3. sum of dot squares = 4               (sum_sq_bob)
  4. ‖x+y‖² ≤ 2(‖x‖² + ‖y‖²)           (parallelogram/triangle)

All proofs are algebraic — BISH-valid.
-/
import Papers.P11_Entanglement.InvolutionNorm
import Mathlib.Data.Complex.BigOperators

namespace Papers.P11

open scoped Matrix Kronecker
open Matrix

noncomputable section

-- ========================================================================
-- Helper: Hermiticity of sum/difference of Hermitian involutions
-- ========================================================================

theorem hermitian_add_involution (B B' : Involution 2) :
    (B.mat + B'.mat).conjTranspose = B.mat + B'.mat := by
  rw [conjTranspose_add, B.hermitian, B'.hermitian]

theorem hermitian_sub_involution (B B' : Involution 2) :
    (B.mat - B'.mat).conjTranspose = B.mat - B'.mat := by
  rw [conjTranspose_sub, B.hermitian, B'.hermitian]

-- ========================================================================
-- Sum of dot-product squares = 4 (the algebraic heart)
-- ========================================================================

/-- The sum of dot-product norms of (I⊗P)v and (I⊗Q)v equals 4,
    where P = B+B', Q = B-B', and ψ is a unit vector. -/
theorem sum_dot_sq_eq_four (B B' : Involution 2)
    (v : Fin 2 × Fin 2 → ℂ) (hv : star v ⬝ᵥ v = 1) :
    star (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (B.mat + B'.mat)).mulVec v) ⬝ᵥ
      (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (B.mat + B'.mat)).mulVec v) +
    star (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (B.mat - B'.mat)).mulVec v) ⬝ᵥ
      (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (B.mat - B'.mat)).mulVec v) = 4 := by
  -- Each term: star(M*ᵥv) ⬝ᵥ (M*ᵥv) = star v ⬝ᵥ ((MᴴM) *ᵥ v)
  have factor : ∀ (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
      dotProduct (star (M.mulVec v)) (M.mulVec v) =
      dotProduct (star v) ((M.conjTranspose * M).mulVec v) := by
    intro M
    simp only [star_mulVec, dotProduct_mulVec, vecMul_vecMul]
  rw [factor, factor]
  rw [← dotProduct_add, ← add_mulVec]
  have hP := hermitian_add_involution B B'
  have hQ := hermitian_sub_involution B B'
  set P := B.mat + B'.mat
  set Q := B.mat - B'.mat
  have hMP : ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ P).conjTranspose *
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ P) = (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (P * P) := by
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, one_mul]
    congr 1; rw [hP]
  have hMQ : ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Q).conjTranspose *
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Q) = (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (Q * Q) := by
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, one_mul]
    congr 1; rw [hQ]
  rw [hMP, hMQ, ← kronecker_add, sum_sq_bob B B', Matrix.kronecker_smul, one_kronecker_one]
  rw [Matrix.smul_mulVec, dotProduct_smul, one_mulVec, hv]
  simp

-- ========================================================================
-- Tsirelson norm-squared identity
-- ========================================================================

/-- star((A⊗P)ψ)⬝ᵥ((A⊗P)ψ) + star((A'⊗Q)ψ)⬝ᵥ((A'⊗Q)ψ) = 4. -/
theorem tsirelson_norm_sq_identity (A A' B B' : Involution 2)
    (v : Fin 2 × Fin 2 → ℂ) (hv : star v ⬝ᵥ v = 1) :
    star ((A.mat ⊗ₖ (B.mat + B'.mat)).mulVec v) ⬝ᵥ
      ((A.mat ⊗ₖ (B.mat + B'.mat)).mulVec v) +
    star ((A'.mat ⊗ₖ (B.mat - B'.mat)).mulVec v) ⬝ᵥ
      ((A'.mat ⊗ₖ (B.mat - B'.mat)).mulVec v) = 4 := by
  rw [involution_tensor_dotProduct_eq A, involution_tensor_dotProduct_eq A']
  exact sum_dot_sq_eq_four B B' v hv

-- ========================================================================
-- Dot-product norm parallelogram bound
-- ========================================================================

/-- For complex vectors: re(star(x+y) ⬝ᵥ (x+y)) ≤ 2*(re(star x ⬝ᵥ x) + re(star y ⬝ᵥ y)).
    This is ‖x+y‖² ≤ 2(‖x‖² + ‖y‖²), which follows from ‖x−y‖² ≥ 0. -/
theorem re_dotProduct_add_le {n : Type*} [Fintype n]
    (x y : n → ℂ) :
    (star (x + y) ⬝ᵥ (x + y)).re ≤
    2 * ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re) := by
  -- ‖x+y‖² + ‖x-y‖² = 2(‖x‖² + ‖y‖²) and ‖x-y‖² ≥ 0
  -- So ‖x+y‖² ≤ 2(‖x‖² + ‖y‖²)
  -- Unfold everything as sums
  simp only [dotProduct, Pi.star_apply, Pi.add_apply]
  -- Goal: (∑ i, star(x_i+y_i)*(x_i+y_i)).re ≤ 2*((∑ i, star(x_i)*x_i).re + (∑ i, star(y_i)*y_i).re)
  -- Pull .re inside sums
  simp only [Complex.re_sum]
  -- Pointwise: re(conj(a+b)*(a+b)) ≤ 2*(re(conj(a)*a) + re(conj(b)*b))
  suffices h : ∀ i, (star (x i + y i) * (x i + y i)).re ≤
      2 * ((star (x i) * x i).re + (star (y i) * y i).re) by
    calc ∑ i, (star (x i + y i) * (x i + y i)).re
        ≤ ∑ i, (2 * ((star (x i) * x i).re + (star (y i) * y i).re)) :=
          Finset.sum_le_sum (fun i _ => h i)
      _ = 2 * (∑ i, (star (x i) * x i).re + ∑ i, (star (y i) * y i).re) := by
          simp_rw [← Finset.sum_add_distrib, ← Finset.mul_sum]
  intro i
  -- star z = conj z for z : ℂ. Expand conj(a+b)*(a+b) and conj(a)*a and conj(b)*b
  have hre : (star (x i + y i) * (x i + y i)).re =
      (x i).re ^ 2 + (x i).im ^ 2 + (y i).re ^ 2 + (y i).im ^ 2 +
      2 * ((x i).re * (y i).re + (x i).im * (y i).im) := by
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
               Complex.add_re, Complex.add_im]
    ring
  have hx : (star (x i) * x i).re = (x i).re ^ 2 + (x i).im ^ 2 := by
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
  have hy : (star (y i) * y i).re = (y i).re ^ 2 + (y i).im ^ 2 := by
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
  rw [hre, hx, hy]
  nlinarith [sq_nonneg ((x i).re - (y i).re), sq_nonneg ((x i).im - (y i).im)]

-- ========================================================================
-- The Tsirelson bound
-- ========================================================================

/-- **Tsirelson bound (Theorem, Part A).**

    For any self-adjoint involutions A, A' (Alice) and B, B' (Bob) on ℂ²,
    and any unit vector ψ ∈ ℂ² ⊗ ℂ² (i.e. star ψ ⬝ᵥ ψ = 1):

      re(star(Cψ) ⬝ᵥ (Cψ)) ≤ 8

    equivalently, ‖Cψ‖² ≤ 8, which implies |⟨ψ|C|ψ⟩| ≤ 2√2.

    Proof:
    1. C = A⊗P + A'⊗Q where P=B+B', Q=B-B'
    2. ‖Cv‖² ≤ 2(‖(A⊗P)v‖² + ‖(A'⊗Q)v‖²)     [‖x+y‖² ≤ 2(‖x‖²+‖y‖²)]
    3. ‖(A⊗P)v‖² + ‖(A'⊗Q)v‖² = 4               [identity]
    4. Therefore ‖Cv‖² ≤ 8                         -/
theorem tsirelson_bound (A A' B B' : Involution 2)
    (v : Fin 2 × Fin 2 → ℂ) (hv : star v ⬝ᵥ v = 1) :
    (star ((chshOperator A A' B B').mulVec v) ⬝ᵥ
     ((chshOperator A A' B B').mulVec v)).re ≤ 8 := by
  -- Step 1: Decompose C = A⊗P + A'⊗Q
  rw [chsh_decomp, add_mulVec]
  -- Step 2: ‖x+y‖² ≤ 2(‖x‖² + ‖y‖²)
  set x := (A.mat ⊗ₖ (B.mat + B'.mat)).mulVec v
  set y := (A'.mat ⊗ₖ (B.mat - B'.mat)).mulVec v
  calc (star (x + y) ⬝ᵥ (x + y)).re
      ≤ 2 * ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re) := re_dotProduct_add_le x y
    _ = 2 * (star x ⬝ᵥ x + star y ⬝ᵥ y).re := by rw [Complex.add_re]
    _ = 2 * (4 : ℂ).re := by
        rw [tsirelson_norm_sq_identity A A' B B' v hv]
    _ = 8 := by norm_num

end

end Papers.P11
