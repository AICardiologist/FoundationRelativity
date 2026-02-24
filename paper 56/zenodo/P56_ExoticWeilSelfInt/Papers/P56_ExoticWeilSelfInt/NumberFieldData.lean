/-
  Paper 56 — Module 1: NumberFieldData
  Exotic Weil Class Self-Intersection on CM Abelian Fourfolds

  All exact arithmetic for the three number fields F₁ = Q(ζ₇ + ζ₇⁻¹),
  F₂ = Q(ζ₉ + ζ₉⁻¹), and F₃ ⊂ Q(ζ₁₃)⁺. This is the computational core.

  Sorry budget: 0. All arithmetic is exact rational, machine-checkable.

  Paul C.-K. Lee, February 2026
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Number Field Data

Exact trace matrices and discriminant computations for:
- F₁ = Q(ζ₇ + ζ₇⁻¹), minimal polynomial t³ + t² − 2t − 1
- F₂ = Q(ζ₉ + ζ₉⁻¹), minimal polynomial t³ − 3t + 1
- F₃ ⊂ Q(ζ₁₃)⁺, minimal polynomial t³ + t² − 4t + 1

All arithmetic is over ℚ. Zero sorries.
-/

-- ============================================================
-- Example 1: F₁ = Q(ζ₇ + ζ₇⁻¹)
-- ============================================================

-- Minimal polynomial of F₁: t³ + t² − 2t − 1 = 0.
-- Elementary symmetric polynomials: e₁ = −1, e₂ = −2, e₃ = 1.

/-- Power sums of the roots of t³ + t² − 2t − 1, computed via Newton's identities.
  p₁ = e₁ = −1
  p₂ = p₁·e₁ − 2·e₂ = (−1)(−1) − 2(−2) = 1 + 4 = 5
  p₃ = p₂·e₁ − p₁·e₂ + 3·e₃ = 5(−1) − (−1)(−2) + 3(1) = −5 − 2 + 3 = −4
  p₄ = p₃·e₁ − p₂·e₂ + p₁·e₃ = (−4)(−1) − 5(−2) + (−1)(1) = 4 + 10 − 1 = 13 -/
def F1_powerSums : Fin 5 → ℚ
  | 0 => 3    -- p₀ = [F:Q] = 3
  | 1 => -1   -- p₁
  | 2 => 5    -- p₂
  | 3 => -4   -- p₃
  | 4 => 13   -- p₄

/-- Trace matrix M₁ for basis {1, t, t²} of F₁/Q.
  M₁[i,j] = Tr(t^{i+j}) = p_{i+j}. -/
def F1_traceMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  !![3, -1, 5; -1, 5, -4; 5, -4, 13]

/-- **disc(F₁) = 49.** Machine-verified determinant computation.

  det(M₁) = 3(5·13 − (−4)²) − (−1)((−1)·13 − (−4)·5) + 5((−1)(−4) − 5·5)
           = 3(65 − 16) + 1(−13 + 20) + 5(4 − 25)
           = 3·49 + 7 + 5·(−21)
           = 147 + 7 − 105 = 49. -/
theorem F1_disc : F1_traceMatrix.det = 49 := by native_decide

-- ============================================================
-- Example 2: F₂ = Q(ζ₉ + ζ₉⁻¹)
-- ============================================================

-- Minimal polynomial of F₂: t³ − 3t + 1 = 0.
-- Elementary symmetric polynomials: e₁ = 0, e₂ = −3, e₃ = −1.

/-- Power sums for t³ − 3t + 1 via Newton's identities.
  p₁ = 0
  p₂ = 0 − 2(−3) = 6
  p₃ = 0 − 0 + 3(−1) = −3
  p₄ = 0 − 6(−3) + 0 = 18 -/
def F2_powerSums : Fin 5 → ℚ
  | 0 => 3    -- p₀ = [F:Q] = 3
  | 1 => 0    -- p₁
  | 2 => 6    -- p₂
  | 3 => -3   -- p₃
  | 4 => 18   -- p₄

/-- Trace matrix M₂ for basis {1, t, t²} of F₂/Q. -/
def F2_traceMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  !![3, 0, 6; 0, 6, -3; 6, -3, 18]

/-- **disc(F₂) = 81.** Machine-verified determinant computation.

  det(M₂) = 3(6·18 − (−3)²) − 0 + 6(0·(−3) − 6·6)
           = 3(108 − 9) + 6(−36)
           = 297 − 216 = 81. -/
theorem F2_disc : F2_traceMatrix.det = 81 := by native_decide

-- ============================================================
-- Example 3: F₃ ⊂ Q(ζ₁₃)⁺
-- ============================================================

-- Minimal polynomial of F₃: t³ + t² − 4t + 1 = 0.
-- Elementary symmetric polynomials: e₁ = −1, e₂ = −4, e₃ = −1.

/-- Power sums for t³ + t² − 4t + 1 via Newton's identities.
  p₁ = e₁ = −1
  p₂ = p₁·e₁ − 2·e₂ = (−1)(−1) − 2(−4) = 1 + 8 = 9
  p₃ = p₂·e₁ − p₁·e₂ + 3·e₃ = 9(−1) − (−1)(−4) + 3(−1) = −9 − 4 − 3 = −16
  p₄ = p₃·e₁ − p₂·e₂ + p₁·e₃ = (−16)(−1) − 9(−4) + (−1)(−1) = 16 + 36 + 1 = 53 -/
def F3_powerSums : Fin 5 → ℚ
  | 0 => 3    -- p₀ = [F:Q] = 3
  | 1 => -1   -- p₁
  | 2 => 9    -- p₂
  | 3 => -16  -- p₃
  | 4 => 53   -- p₄

/-- Trace matrix M₃ for basis {1, t, t²} of F₃/Q. -/
def F3_traceMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  !![3, -1, 9; -1, 9, -16; 9, -16, 53]

/-- **disc(F₃) = 169.** Machine-verified determinant computation.

  det(M₃) = 3(9·53 − (−16)²) − (−1)((−1)·53 − (−16)·9) + 9((−1)(−16) − 9·9)
           = 3(477 − 256) + 1(−53 + 144) + 9(16 − 81)
           = 3·221 + 91 + 9·(−65)
           = 663 + 91 − 585 = 169. -/
theorem F3_disc : F3_traceMatrix.det = 169 := by native_decide

-- ============================================================
-- Verification of Newton's identity intermediate steps
-- ============================================================

/-- Newton's identity step: p₂ for F₁. -/
theorem F1_newton_p2 : (-1 : ℚ) * (-1) - 2 * (-2) = 5 := by norm_num

/-- Newton's identity step: p₃ for F₁. -/
theorem F1_newton_p3 : (5 : ℚ) * (-1) - (-1) * (-2) + 3 * 1 = -4 := by norm_num

/-- Newton's identity step: p₄ for F₁. -/
theorem F1_newton_p4 : (-4 : ℚ) * (-1) - 5 * (-2) + (-1) * 1 = 13 := by norm_num

/-- Newton's identity step: p₂ for F₂. -/
theorem F2_newton_p2 : (0 : ℚ) * 0 - 2 * (-3) = 6 := by norm_num

/-- Newton's identity step: p₃ for F₂. -/
theorem F2_newton_p3 : (6 : ℚ) * 0 - 0 * (-3) + 3 * (-1) = -3 := by norm_num

/-- Newton's identity step: p₄ for F₂. -/
theorem F2_newton_p4 : (-3 : ℚ) * 0 - 6 * (-3) + 0 * (-1) = 18 := by norm_num

/-- Newton's identity step: p₂ for F₃. -/
theorem F3_newton_p2 : (-1 : ℚ) * (-1) - 2 * (-4) = 9 := by norm_num

/-- Newton's identity step: p₃ for F₃. -/
theorem F3_newton_p3 : (9 : ℚ) * (-1) - (-1) * (-4) + 3 * (-1) = -16 := by norm_num

/-- Newton's identity step: p₄ for F₃. -/
theorem F3_newton_p4 : (-16 : ℚ) * (-1) - 9 * (-4) + (-1) * (-1) = 53 := by norm_num

-- ============================================================
-- Perfect square verification
-- ============================================================

/-- 49 = 7². -/
theorem disc_F1_perfect_square : (49 : ℤ) = 7 * 7 := by norm_num

/-- 81 = 9². -/
theorem disc_F2_perfect_square : (81 : ℤ) = 9 * 9 := by norm_num

/-- 169 = 13². -/
theorem disc_F3_perfect_square : (169 : ℤ) = 13 * 13 := by norm_num
