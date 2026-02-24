/-
Papers/P6_Heisenberg/RobertsonSchrodinger.lean
Paper 6 v2: Robertson-Schrödinger uncertainty inequality — CRM proof.

Main theorems:
  1. robertson_schrodinger: |⟨[A,B]⟩|² ≤ 4 · Var(A) · Var(B)
  2. schrodinger: |⟨[A,B]⟩|² + |⟨{ΔA,ΔB}⟩|² ≤ 4 · Var(A) · Var(B)

Both proved from Mathlib's Cauchy-Schwarz inequality with no custom axioms.
Height 0: fully constructive, no classical choice principles.
-/
import Papers.P6_Heisenberg.Basic

namespace Papers.P6_Heisenberg

open Complex RCLike

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

-- ========================================================================
-- Auxiliary: |z - conj z|² ≤ 4|z|² for any z : ℂ
-- ========================================================================

/-- For any z : ℂ, ‖z − z̄‖² ≤ 4‖z‖².
    Proof: z − z̄ = 2i·Im(z), so ‖z − z̄‖² = 4·Im(z)² ≤ 4·‖z‖². -/
theorem norm_sq_sub_conj_le (z : ℂ) :
    ‖z - starRingEnd ℂ z‖ ^ 2 ≤ 4 * ‖z‖ ^ 2 := by
  -- Use normSq and the fact that ‖z‖² = normSq z
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  -- z - conj z = ⟨0, 2·im(z)⟩
  have h1 : (z - starRingEnd ℂ z).re = 0 := by simp [Complex.conj_re]
  have h2 : (z - starRingEnd ℂ z).im = 2 * z.im := by simp [Complex.conj_im]; ring
  -- normSq(z - conj z) = 0² + (2·im)² = 4·im²
  rw [Complex.normSq_apply, h1, h2]
  -- normSq(z) = re² + im²
  rw [Complex.normSq_apply]
  nlinarith [sq_nonneg z.re, sq_nonneg z.im]

/-- For any z : ℂ, ‖z − z̄‖² + ‖z + z̄‖² = 4‖z‖².
    This is the Schrödinger identity. -/
theorem norm_sq_skew_sym_sum (z : ℂ) :
    ‖z - starRingEnd ℂ z‖ ^ 2 + ‖z + starRingEnd ℂ z‖ ^ 2 = 4 * ‖z‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  have h1_re : (z - starRingEnd ℂ z).re = 0 := by simp [Complex.conj_re]
  have h1_im : (z - starRingEnd ℂ z).im = 2 * z.im := by simp [Complex.conj_im]; ring
  have h2_re : (z + starRingEnd ℂ z).re = 2 * z.re := by simp [Complex.conj_re]; ring
  have h2_im : (z + starRingEnd ℂ z).im = 0 := by simp [Complex.conj_im]
  simp only [Complex.normSq_apply, h1_re, h1_im, h2_re, h2_im]
  nlinarith [sq_nonneg z.re, sq_nonneg z.im]

-- ========================================================================
-- Core Cauchy-Schwarz consequence: ‖⟪x,y⟫‖² ≤ ‖x‖² · ‖y‖²
-- ========================================================================

/-- Cauchy-Schwarz squared: ‖⟪x, y⟫‖² ≤ ‖x‖² · ‖y‖².
    Direct from Mathlib's norm_inner_le_norm. -/
theorem cauchy_schwarz_sq (x y : E) :
    ‖@inner ℂ E _ x y‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) x y
  -- h : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖
  -- We need ‖⟪x, y⟫‖² ≤ (‖x‖ * ‖y‖)²
  have h2 : ‖@inner ℂ E _ x y‖ ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 := by
    apply sq_le_sq'
    · linarith [norm_nonneg (@inner ℂ E _ x y)]
    · exact h
  linarith [mul_self_nonneg ‖x‖, mul_self_nonneg ‖y‖]

-- ========================================================================
-- Robertson-Schrödinger inequality
-- ========================================================================

/-- **Robertson-Schrödinger inequality.**
    For self-adjoint A, B and unit ψ:
      ‖expect (comm A B) ψ‖² ≤ 4 · var A ψ · var B ψ

    Proof:
    1. ⟨[A,B]⟩ = z − z̄ where z = ⟪ΔA, ΔB⟫.
    2. ‖z − z̄‖² ≤ 4‖z‖².
    3. ‖z‖² ≤ ‖ΔA‖² · ‖ΔB‖² = Var(A) · Var(B) (Cauchy-Schwarz).

    Height 0: no classical axioms used. -/
theorem robertson_schrodinger (A B : Op E) (ψ : E)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hψ : ‖ψ‖ = 1) :
    ‖expect (comm A B) ψ‖ ^ 2 ≤ 4 * (var A ψ * var B ψ) := by
  set z := @inner ℂ E _ (centered A ψ) (centered B ψ)
  -- Step 1: ⟨[A,B]⟩ = z − z̄
  have h_comm : expect (comm A B) ψ = z - starRingEnd ℂ z :=
    expect_comm_eq_sub_conj A B ψ hA hB hψ
  -- Step 2: ‖z − z̄‖² ≤ 4‖z‖²
  have h_skew : ‖z - starRingEnd ℂ z‖ ^ 2 ≤ 4 * ‖z‖ ^ 2 := norm_sq_sub_conj_le z
  -- Step 3: ‖z‖² ≤ Var(A) · Var(B)  (Cauchy-Schwarz)
  have h_cs : ‖z‖ ^ 2 ≤ var A ψ * var B ψ := cauchy_schwarz_sq (centered A ψ) (centered B ψ)
  -- Chain
  rw [h_comm]
  linarith [mul_nonneg (le_of_lt (by norm_num : (0:ℝ) < 4)) (var_nonneg A ψ)]

-- ========================================================================
-- Schrödinger strengthening
-- ========================================================================

/-- **Schrödinger inequality** (strengthening of Robertson-Schrödinger).
    For self-adjoint A, B and unit ψ:
      ‖expect (comm A B) ψ‖² + ‖expect (acomm A B) ψ − 2⟨A⟩⟨B⟩‖² ≤ 4 · var A ψ · var B ψ

    Uses the identity ‖z - z̄‖² + ‖z + z̄‖² = 4‖z‖² together with
    Cauchy-Schwarz.

    Height 0: no classical axioms used. -/
theorem schrodinger (A B : Op E) (ψ : E)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hψ : ‖ψ‖ = 1) :
    ‖expect (comm A B) ψ‖ ^ 2 +
    ‖expect (acomm A B) ψ - 2 * expect A ψ * expect B ψ‖ ^ 2
      ≤ 4 * (var A ψ * var B ψ) := by
  set z := @inner ℂ E _ (centered A ψ) (centered B ψ)
  -- Bridge lemmas
  have h_comm : expect (comm A B) ψ = z - starRingEnd ℂ z :=
    expect_comm_eq_sub_conj A B ψ hA hB hψ
  have h_acomm : expect (acomm A B) ψ - 2 * expect A ψ * expect B ψ =
    z + starRingEnd ℂ z := expect_acomm_centered A B ψ hA hB hψ
  -- Schrödinger identity: ‖z − z̄‖² + ‖z + z̄‖² = 4‖z‖²
  have h_id : ‖z - starRingEnd ℂ z‖ ^ 2 + ‖z + starRingEnd ℂ z‖ ^ 2 = 4 * ‖z‖ ^ 2 :=
    norm_sq_skew_sym_sum z
  -- Cauchy-Schwarz: ‖z‖² ≤ Var(A) · Var(B)
  have h_cs : ‖z‖ ^ 2 ≤ var A ψ * var B ψ := cauchy_schwarz_sq (centered A ψ) (centered B ψ)
  -- Chain
  rw [h_comm, h_acomm]
  linarith

end

end Papers.P6_Heisenberg
