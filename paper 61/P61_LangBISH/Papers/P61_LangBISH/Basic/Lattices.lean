/-
  Paper 61: Lang's Conjecture as the MP → BISH Gate
  Basic/Lattices.lean — Minkowski's Second Theorem and Hermite constants

  Axiomatizes lattice geometry of numbers for the Mordell–Weil lattice.
-/
import Mathlib.Tactic

namespace Papers.P61_LangBISH

/-! ## Hermite Constant -/

/-- The Hermite constant γ_r for dimension r (squared form).
    Known exact values for small dimensions. -/
def hermiteConstant : ℕ → ℚ
  | 1 => 1
  | 2 => 4 / 3
  | 3 => 2
  | 4 => 4
  | 5 => 8
  | 6 => 64 / 3
  | 7 => 64
  | 8 => 256
  | _ => 0  -- placeholder; only small dimensions needed

theorem hermiteConstant_two : hermiteConstant 2 = 4 / 3 := rfl

theorem hermiteConstant_pos (r : ℕ) (hr : 1 ≤ r) (hr' : r ≤ 8) :
    hermiteConstant r > 0 := by
  interval_cases r <;> simp [hermiteConstant] <;> norm_num

/-! ## Successive Minima and Minkowski's Second Theorem -/

/-- Successive minima of a rank-r Mordell–Weil lattice.
    λ₁ ≤ λ₂ ≤ ⋯ ≤ λ_r are the canonical heights of the
    shortest independent vectors. -/
structure SuccessiveMinima (r : ℕ) where
  lambda : Fin r → ℚ
  ordered : ∀ i j : Fin r, i ≤ j → lambda i ≤ lambda j
  all_pos : ∀ i : Fin r, lambda i > 0

/-- Minkowski's Second Theorem: the product of successive minima is bounded
    by γ_r^{r/2} · √R, where R is the regulator (covolume squared).

    We axiomatize the rational version: ∏ λ_i ≤ hermite_bound · sqrt_reg,
    where sqrt_reg² ≤ R (a rational approximation to √R). -/
axiom minkowski_second_theorem (r : ℕ) (hr : r ≥ 1)
    (sm : SuccessiveMinima r)
    (sqrt_reg : ℚ) (h_sqrt : sqrt_reg > 0)
    (R : ℚ) (hR : R > 0) (h_approx : sqrt_reg * sqrt_reg ≤ R) :
    (Finset.univ.prod sm.lambda) ≤ (hermiteConstant r) ^ (r / 2) * sqrt_reg

end Papers.P61_LangBISH
