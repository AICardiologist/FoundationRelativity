/-
  TraceData.lean — Ring-verified identities for Paper 89
  Auto-generated from emit_lean_data.py

  Universal family: y² = x⁹ + ax⁷ + bx⁵ + cx³ + x
  Key result: τ₊ = 0 for all three parameter directions
-/

import Mathlib

/-- τ+ vanishing in ∂/∂a: numerators over common denominator sum to 0. -/
theorem p89_tau_plus_a_vanishes (a b c : ℤ) :
    (- 9 * a ^ 3 + a ^ 2 * b * c + 32 * a * b + 3 * a * c ^ 2 - 4 * b ^ 2 * c - 48 * c)
    + (- 45 * a ^ 3 + 23 * a ^ 2 * b * c - 6 * a ^ 2 * c ^ 3 + 160 * a * b - 9 * a * c ^ 2 - 68 * b ^ 2 * c + 18 * b * c ^ 3 - 48 * c)
    + (- 81 * a ^ 3 + 66 * a ^ 2 * b * c - 14 * a ^ 2 * c ^ 3 - 20 * a * b ^ 3 + 5 * a * b ^ 2 * c ^ 2 + 48 * a * b - 29 * a * c ^ 2 + 12 * b ^ 2 * c - 3 * b * c ^ 3 + 16 * c)
    + (135 * a ^ 3 - 90 * a ^ 2 * b * c + 20 * a ^ 2 * c ^ 3 + 20 * a * b ^ 3 - 5 * a * b ^ 2 * c ^ 2 - 240 * a * b + 35 * a * c ^ 2 + 60 * b ^ 2 * c - 15 * b * c ^ 3 + 80 * c)
    = 0 := by ring

/-- τ- vanishing in ∂/∂a: numerators over common denominator sum to 0. -/
theorem p89_tau_minus_a_vanishes (a b c : ℤ) :
    (- 27 * a ^ 3 + 3 * a ^ 2 * b * c + 96 * a * b + 9 * a * c ^ 2 - 12 * b ^ 2 * c - 144 * c)
    + (- 63 * a ^ 3 + 37 * a ^ 2 * b * c - 10 * a ^ 2 * c ^ 3 + 224 * a * b - 19 * a * c ^ 2 - 108 * b ^ 2 * c + 30 * b * c ^ 3 - 16 * c)
    + (- 99 * a ^ 3 + 86 * a ^ 2 * b * c - 18 * a ^ 2 * c ^ 3 - 28 * a * b ^ 3 + 7 * a * b ^ 2 * c ^ 2 + 16 * a * b - 39 * a * c ^ 2 + 36 * b ^ 2 * c - 9 * b * c ^ 3 + 48 * c)
    + (189 * a ^ 3 - 126 * a ^ 2 * b * c + 28 * a ^ 2 * c ^ 3 + 28 * a * b ^ 3 - 7 * a * b ^ 2 * c ^ 2 - 336 * a * b + 49 * a * c ^ 2 + 84 * b ^ 2 * c - 21 * b * c ^ 3 + 112 * c)
    = 0 := by ring

/-- τ+ vanishing in ∂/∂b: numerators over common denominator sum to 0. -/
theorem p89_tau_plus_b_vanishes (a b c : ℤ) :
    (6 * a ^ 3 * c - 2 * a ^ 2 * b ^ 2 + 12 * a ^ 2 - 28 * a * b * c + 8 * b ^ 3 - 32 * b + 36 * c ^ 2)
    + (3 * a ^ 3 * c - 10 * a ^ 2 * b ^ 2 + 3 * a ^ 2 * b * c ^ 2 + 60 * a ^ 2 - 44 * a * b * c + 9 * a * c ^ 3 + 40 * b ^ 3 - 12 * b ^ 2 * c ^ 2 - 160 * b + 36 * c ^ 2)
    + (- 9 * a ^ 3 * c + 12 * a ^ 2 * b ^ 2 - 3 * a ^ 2 * b * c ^ 2 + 108 * a ^ 2 - 68 * a * b * c + 21 * a * c ^ 3 - 8 * b ^ 3 + 2 * b ^ 2 * c ^ 2 + 32 * b - 12 * c ^ 2)
    + (- 180 * a ^ 2 + 140 * a * b * c - 30 * a * c ^ 3 - 40 * b ^ 3 + 10 * b ^ 2 * c ^ 2 + 160 * b - 60 * c ^ 2)
    = 0 := by ring

/-- τ- vanishing in ∂/∂b: numerators over common denominator sum to 0. -/
theorem p89_tau_minus_b_vanishes (a b c : ℤ) :
    (18 * a ^ 3 * c - 6 * a ^ 2 * b ^ 2 + 36 * a ^ 2 - 84 * a * b * c + 24 * b ^ 3 - 96 * b + 108 * c ^ 2)
    + (- 3 * a ^ 3 * c - 14 * a ^ 2 * b ^ 2 + 5 * a ^ 2 * b * c ^ 2 + 84 * a ^ 2 - 36 * a * b * c + 15 * a * c ^ 3 + 56 * b ^ 3 - 20 * b ^ 2 * c ^ 2 - 224 * b + 12 * c ^ 2)
    + (- 15 * a ^ 3 * c + 20 * a ^ 2 * b ^ 2 - 5 * a ^ 2 * b * c ^ 2 + 132 * a ^ 2 - 76 * a * b * c + 27 * a * c ^ 3 - 24 * b ^ 3 + 6 * b ^ 2 * c ^ 2 + 96 * b - 36 * c ^ 2)
    + (- 252 * a ^ 2 + 196 * a * b * c - 42 * a * c ^ 3 - 56 * b ^ 3 + 14 * b ^ 2 * c ^ 2 + 224 * b - 84 * c ^ 2)
    = 0 := by ring

/-- τ+ vanishing in ∂/∂c: numerators over common denominator sum to 0. -/
theorem p89_tau_plus_c_vanishes (a b c : ℤ) :
    (3 * a ^ 3 * b - 4 * a ^ 3 * c ^ 2 + a ^ 2 * b ^ 2 * c - 7 * a ^ 2 * c - 12 * a * b ^ 2 + 18 * a * b * c ^ 2 - 16 * a - 4 * b ^ 3 * c + 48 * b * c - 27 * c ^ 3)
    + (15 * a ^ 3 * b - 2 * a ^ 3 * c ^ 2 - a ^ 2 * b ^ 2 * c + a ^ 2 * c - 60 * a * b ^ 2 + 6 * a * b * c ^ 2 - 80 * a + 4 * b ^ 3 * c + 144 * b * c - 27 * c ^ 3)
    + (- 18 * a ^ 3 * b + 6 * a ^ 3 * c ^ 2 + 21 * a ^ 2 * c + 52 * a * b ^ 2 - 19 * a * b * c ^ 2 - 144 * a - 32 * b * c + 9 * c ^ 3)
    + (- 15 * a ^ 2 * c + 20 * a * b ^ 2 - 5 * a * b * c ^ 2 + 240 * a - 160 * b * c + 45 * c ^ 3)
    = 0 := by ring

/-- τ- vanishing in ∂/∂c: numerators over common denominator sum to 0. -/
theorem p89_tau_minus_c_vanishes (a b c : ℤ) :
    (9 * a ^ 3 * b - 12 * a ^ 3 * c ^ 2 + 3 * a ^ 2 * b ^ 2 * c - 21 * a ^ 2 * c - 36 * a * b ^ 2 + 54 * a * b * c ^ 2 - 48 * a - 12 * b ^ 3 * c + 144 * b * c - 81 * c ^ 3)
    + (21 * a ^ 3 * b + 2 * a ^ 3 * c ^ 2 - 3 * a ^ 2 * b ^ 2 * c + 11 * a ^ 2 * c - 84 * a * b ^ 2 - 14 * a * b * c ^ 2 - 112 * a + 12 * b ^ 3 * c + 176 * b * c - 9 * c ^ 3)
    + (- 30 * a ^ 3 * b + 10 * a ^ 3 * c ^ 2 + 31 * a ^ 2 * c + 92 * a * b ^ 2 - 33 * a * b * c ^ 2 - 176 * a - 96 * b * c + 27 * c ^ 3)
    + (- 21 * a ^ 2 * c + 28 * a * b ^ 2 - 7 * a * b * c ^ 2 + 336 * a - 224 * b * c + 63 * c ^ 3)
    = 0 := by ring

-- Structural data

def p89_genus : Nat := 4

theorem p89_g_minus_1_odd : p89_genus - 1 = 3 := by rfl

theorem p89_three_is_odd : ¬(2 ∣ (3 : ℤ)) := by decide
