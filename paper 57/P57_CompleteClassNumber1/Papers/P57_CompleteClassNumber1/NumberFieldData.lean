/-
  Paper 57 — Module 1: NumberFieldData
  Complete Class-Number-1 Landscape for Exotic Weil Self-Intersection

  Trace matrices and discriminant computations for ALL NINE totally real
  cubic fields arising from class-number-1 quadratic imaginary fields.

  Three from Paper 56 (d = 1, 3, 7) plus six new (d = 2, 11, 19, 43, 67, 163).

  Sorry budget: 0. All arithmetic is exact rational, machine-checkable.

  Paul C.-K. Lee, February 2026
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Number Field Data — Complete Class-Number-1 Landscape

All nine trace matrices and discriminant computations. The nine
class-number-1 imaginary quadratic fields are:

| d   | K            | F minimal polynomial      | disc(F) |
|-----|--------------|---------------------------|---------|
| 1   | Q(i)         | t³ − 3t + 1               | 81      |
| 2   | Q(√-2)       | t³ + t² − 6t − 7          | 361     |
| 3   | Q(√-3)       | t³ + t² − 2t − 1          | 49      |
| 7   | Q(√-7)       | t³ + t² − 4t + 1          | 169     |
| 11  | Q(√-11)      | t³ − 5t² − 4t + 31        | 1369    |
| 19  | Q(√-19)      | t³ − 18t² + 47t − 33      | 3721    |
| 43  | Q(√-43)      | t³ − 4t² − 21t − 17       | 6241    |
| 67  | Q(√-67)      | t³ − 20t² + 79t − 85      | 26569   |
| 163 | Q(√-163)     | t³ − 5t² − 24t − 19       | 9409    |
-/

-- ============================================================
-- Paper 56 Examples (d = 3, 1, 7)
-- ============================================================

-- Example 1: d = 3, F₁ = Q(ζ₇ + ζ₇⁻¹), t³ + t² − 2t − 1
-- e₁ = −1, e₂ = −2, e₃ = 1
-- p₁ = −1, p₂ = 5, p₃ = −4, p₄ = 13

/-- Trace matrix for F₁ = Q(ζ₇ + ζ₇⁻¹). -/
def F1_traceMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  !![3, -1, 5; -1, 5, -4; 5, -4, 13]

/-- disc(F₁) = 49. -/
theorem F1_disc : F1_traceMatrix.det = 49 := by native_decide

-- Example 2: d = 1, F₂ = Q(ζ₉ + ζ₉⁻¹), t³ − 3t + 1
-- e₁ = 0, e₂ = −3, e₃ = −1
-- p₁ = 0, p₂ = 6, p₃ = −3, p₄ = 18

/-- Trace matrix for F₂ = Q(ζ₉ + ζ₉⁻¹). -/
def F2_traceMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  !![3, 0, 6; 0, 6, -3; 6, -3, 18]

/-- disc(F₂) = 81. -/
theorem F2_disc : F2_traceMatrix.det = 81 := by native_decide

-- Example 3: d = 7, F₃ ⊂ Q(ζ₁₃)⁺, t³ + t² − 4t + 1
-- e₁ = −1, e₂ = −4, e₃ = −1
-- p₁ = −1, p₂ = 9, p₃ = −16, p₄ = 53

/-- Trace matrix for F₃ ⊂ Q(ζ₁₃)⁺. -/
def F3_traceMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  !![3, -1, 9; -1, 9, -16; 9, -16, 53]

/-- disc(F₃) = 169. -/
theorem F3_disc : F3_traceMatrix.det = 169 := by native_decide

-- ============================================================
-- Paper 57 Examples (d = 2, 11, 19, 43, 67, 163)
-- ============================================================

-- Example 4: d = 2, t³ + t² − 6t − 7
-- e₁ = −1, e₂ = −6, e₃ = 7
-- p₁ = −1, p₂ = 13, p₃ = 2, p₄ = 69

/-- Trace matrix for the totally real cubic with min poly t³ + t² − 6t − 7. -/
def F4_traceMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  !![3, -1, 13; -1, 13, 2; 13, 2, 69]

/-- **disc(F₄) = 361 = 19².** -/
theorem F4_disc : F4_traceMatrix.det = 361 := by native_decide

-- Example 5: d = 11, t³ − 5t² − 4t + 31
-- e₁ = 5, e₂ = −4, e₃ = −31
-- p₁ = 5, p₂ = 33, p₃ = 92, p₄ = 437

/-- Trace matrix for the totally real cubic with min poly t³ − 5t² − 4t + 31. -/
def F5_traceMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  !![3, 5, 33; 5, 33, 92; 33, 92, 437]

/-- **disc(F₅) = 1369 = 37².** -/
theorem F5_disc : F5_traceMatrix.det = 1369 := by native_decide

-- Example 6: d = 19, t³ − 18t² + 47t − 33
-- e₁ = 18, e₂ = 47, e₃ = 33
-- p₁ = 18, p₂ = 230, p₃ = 3393, p₄ = 50858

/-- Trace matrix for the totally real cubic with min poly t³ − 18t² + 47t − 33. -/
def F6_traceMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  !![3, 18, 230; 18, 230, 3393; 230, 3393, 50858]

/-- **disc(F₆) = 3721 = 61².** -/
theorem F6_disc : F6_traceMatrix.det = 3721 := by native_decide

-- Example 7: d = 43, t³ − 4t² − 21t − 17
-- e₁ = 4, e₂ = −21, e₃ = 17
-- p₁ = 4, p₂ = 58, p₃ = 367, p₄ = 2754

/-- Trace matrix for the totally real cubic with min poly t³ − 4t² − 21t − 17. -/
def F7_traceMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  !![3, 4, 58; 4, 58, 367; 58, 367, 2754]

/-- **disc(F₇) = 6241 = 79².** -/
theorem F7_disc : F7_traceMatrix.det = 6241 := by native_decide

-- Example 8: d = 67, t³ − 20t² + 79t − 85
-- e₁ = 20, e₂ = 79, e₃ = 85
-- p₁ = 20, p₂ = 242, p₃ = 3515, p₄ = 52882

/-- Trace matrix for the totally real cubic with min poly t³ − 20t² + 79t − 85. -/
def F8_traceMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  !![3, 20, 242; 20, 242, 3515; 242, 3515, 52882]

/-- **disc(F₈) = 26569 = 163².** -/
theorem F8_disc : F8_traceMatrix.det = 26569 := by native_decide

-- Example 9: d = 163, t³ − 5t² − 24t − 19
-- e₁ = 5, e₂ = −24, e₃ = 19
-- p₁ = 5, p₂ = 73, p₃ = 542, p₄ = 4557

/-- Trace matrix for the totally real cubic with min poly t³ − 5t² − 24t − 19. -/
def F9_traceMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  !![3, 5, 73; 5, 73, 542; 73, 542, 4557]

/-- **disc(F₉) = 9409 = 97².** -/
theorem F9_disc : F9_traceMatrix.det = 9409 := by native_decide

-- ============================================================
-- Newton's identity verification (all nine fields)
-- ============================================================

-- F₁: e₁ = −1, e₂ = −2, e₃ = 1
theorem F1_newton_p2 : (-1 : ℚ) * (-1) - 2 * (-2) = 5 := by norm_num
theorem F1_newton_p3 : (5 : ℚ) * (-1) - (-1) * (-2) + 3 * 1 = -4 := by norm_num
theorem F1_newton_p4 : (-4 : ℚ) * (-1) - 5 * (-2) + (-1) * 1 = 13 := by norm_num

-- F₂: e₁ = 0, e₂ = −3, e₃ = −1
theorem F2_newton_p2 : (0 : ℚ) * 0 - 2 * (-3) = 6 := by norm_num
theorem F2_newton_p3 : (6 : ℚ) * 0 - 0 * (-3) + 3 * (-1) = -3 := by norm_num
theorem F2_newton_p4 : (-3 : ℚ) * 0 - 6 * (-3) + 0 * (-1) = 18 := by norm_num

-- F₃: e₁ = −1, e₂ = −4, e₃ = −1
theorem F3_newton_p2 : (-1 : ℚ) * (-1) - 2 * (-4) = 9 := by norm_num
theorem F3_newton_p3 : (9 : ℚ) * (-1) - (-1) * (-4) + 3 * (-1) = -16 := by norm_num
theorem F3_newton_p4 : (-16 : ℚ) * (-1) - 9 * (-4) + (-1) * (-1) = 53 := by norm_num

-- F₄: e₁ = −1, e₂ = −6, e₃ = 7
theorem F4_newton_p2 : (-1 : ℚ) * (-1) - 2 * (-6) = 13 := by norm_num
theorem F4_newton_p3 : (13 : ℚ) * (-1) - (-1) * (-6) + 3 * 7 = -13 - 6 + 21 := by norm_num
theorem F4_newton_p3' : (-1 : ℚ) * 13 - (-6) * (-1) + 3 * 7 = 2 := by norm_num
theorem F4_newton_p4 : (2 : ℚ) * (-1) - 13 * (-6) + (-1) * 7 = 69 := by norm_num

-- F₅: e₁ = 5, e₂ = −4, e₃ = −31
theorem F5_newton_p2 : (5 : ℚ) * 5 - 2 * (-4) = 33 := by norm_num
theorem F5_newton_p3 : (33 : ℚ) * 5 - (-4) * 5 + 3 * (-31) = 92 := by norm_num
theorem F5_newton_p4 : (92 : ℚ) * 5 - (-4) * 33 + (-31) * 5 = 437 := by norm_num

-- F₆: e₁ = 18, e₂ = 47, e₃ = 33
theorem F6_newton_p2 : (18 : ℚ) * 18 - 2 * 47 = 230 := by norm_num
theorem F6_newton_p3 : (230 : ℚ) * 18 - 47 * 18 + 3 * 33 = 3393 := by norm_num
theorem F6_newton_p4 : (3393 : ℚ) * 18 - 47 * 230 + 33 * 18 = 50858 := by norm_num

-- F₇: e₁ = 4, e₂ = −21, e₃ = 17
theorem F7_newton_p2 : (4 : ℚ) * 4 - 2 * (-21) = 58 := by norm_num
theorem F7_newton_p3 : (58 : ℚ) * 4 - (-21) * 4 + 3 * 17 = 367 := by norm_num
theorem F7_newton_p4 : (367 : ℚ) * 4 - (-21) * 58 + 17 * 4 = 2754 := by norm_num

-- F₈: e₁ = 20, e₂ = 79, e₃ = 85
theorem F8_newton_p2 : (20 : ℚ) * 20 - 2 * 79 = 242 := by norm_num
theorem F8_newton_p3 : (242 : ℚ) * 20 - 79 * 20 + 3 * 85 = 3515 := by norm_num
theorem F8_newton_p4 : (3515 : ℚ) * 20 - 79 * 242 + 85 * 20 = 52882 := by norm_num

-- F₉: e₁ = 5, e₂ = −24, e₃ = 19
theorem F9_newton_p2 : (5 : ℚ) * 5 - 2 * (-24) = 73 := by norm_num
theorem F9_newton_p3 : (73 : ℚ) * 5 - (-24) * 5 + 3 * 19 = 542 := by norm_num
theorem F9_newton_p4 : (542 : ℚ) * 5 - (-24) * 73 + 19 * 5 = 4557 := by norm_num

-- ============================================================
-- Perfect square verification (all nine)
-- ============================================================

theorem disc_F1_square : (7 : ℤ) ^ 2 = 49 := by norm_num
theorem disc_F2_square : (9 : ℤ) ^ 2 = 81 := by norm_num
theorem disc_F3_square : (13 : ℤ) ^ 2 = 169 := by norm_num
theorem disc_F4_square : (19 : ℤ) ^ 2 = 361 := by norm_num
theorem disc_F5_square : (37 : ℤ) ^ 2 = 1369 := by norm_num
theorem disc_F6_square : (61 : ℤ) ^ 2 = 3721 := by norm_num
theorem disc_F7_square : (79 : ℤ) ^ 2 = 6241 := by norm_num
theorem disc_F8_square : (163 : ℤ) ^ 2 = 26569 := by norm_num
theorem disc_F9_square : (97 : ℤ) ^ 2 = 9409 := by norm_num
