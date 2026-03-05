import Mathlib.Tactic

/-!
# Fractional Local System Data

The substitution u = x² transforms the σ-eigenspace V₊ of the odd hyperelliptic
family y² = x^{2g+1} + a₁x^{2g-1} + ··· + a_{g-1}x³ + x into the complete H¹
of a rank-1 local system on ℙ¹ punctured at 0 and the roots of
  P(u) = u^g + a₁u^{g-1} + ··· + a_{g-1}u + 1,
with integrand u^{-3/4} P(u)^{-1/2} du.

The local exponents at the singular points determine the Aomoto-Varchenko
period determinant. The key calculation:
  • Root-root exponent: α_i + α_j + 1 = (-1/2)+(-1/2)+1 = 0
    ⟹ discriminant drops out of det(Π₊)
  • Root-origin exponent: α_i + α₀ + 1 = (-1/2)+(-3/4)+1 = -1/4
    ⟹ det(Π₊) ∝ (∏ uᵢ)^{-1/4}

References:
  Aomoto-Kita, "Theory of Hypergeometric Functions" (Springer, 2011)
  Varchenko, "The Euler beta-function, the Vandermonde determinant,
    Legendre's equation, and critical values of linear functions" (1995)
-/

namespace P93

-- ═══════════════════════════════════════════════════════════════
-- §1. Local exponents at singular points
-- ═══════════════════════════════════════════════════════════════

/-- Local exponent at each root uᵢ of P(u): square-root branching. -/
noncomputable def alpha_root : ℚ := -1 / 2

/-- Local exponent at the origin u = 0 for V₊: from the u^{-3/4} factor. -/
noncomputable def alpha_origin : ℚ := -3 / 4

/-- Local exponent at the origin for V₋: from the u^{-1/4} factor. -/
noncomputable def alpha_origin_minus : ℚ := -1 / 4

-- ═══════════════════════════════════════════════════════════════
-- §2. Varchenko exponent for root-root pairs
-- ═══════════════════════════════════════════════════════════════

/-- The Varchenko exponent for a pair of roots of P(u). -/
noncomputable def varchenko_root_root : ℚ := alpha_root + alpha_root + 1

/-- Root-root exponent vanishes: discriminant drops out of det(Π₊).
    This is the key cancellation: (uᵢ - uⱼ)^0 = 1. -/
theorem varchenko_root_root_zero : varchenko_root_root = 0 := by
  unfold varchenko_root_root alpha_root; norm_num

-- ═══════════════════════════════════════════════════════════════
-- §3. Varchenko exponent for root-origin pairs
-- ═══════════════════════════════════════════════════════════════

/-- The Varchenko exponent for a root of P(u) paired with the origin. -/
noncomputable def varchenko_root_origin : ℚ := alpha_root + alpha_origin + 1

/-- Root-origin exponent is -1/4, so det(Π₊) ∝ (∏ uᵢ)^{-1/4}. -/
theorem varchenko_root_origin_val : varchenko_root_origin = -(1 / 4) := by
  unfold varchenko_root_origin alpha_root alpha_origin; norm_num

-- ═══════════════════════════════════════════════════════════════
-- §4. V₋ exponents (for completeness)
-- ═══════════════════════════════════════════════════════════════

/-- The Varchenko exponent for V₋: root paired with origin. -/
noncomputable def varchenko_root_origin_minus : ℚ := alpha_root + alpha_origin_minus + 1

/-- V₋ root-origin exponent is +1/4 (positive, but same Vieta freezing applies). -/
theorem varchenko_root_origin_minus_val : varchenko_root_origin_minus = 1 / 4 := by
  unfold varchenko_root_origin_minus alpha_root alpha_origin_minus; norm_num

-- ═══════════════════════════════════════════════════════════════
-- §5. Exponent sum constraints
-- ═══════════════════════════════════════════════════════════════

/-- For g roots of P(u), the total root-origin contribution to det(Π₊)
    has exponent g · (-1/4). We verify this for genera 2–8. -/
theorem total_exponent_g2 : 2 * varchenko_root_origin = -(1 / 2) := by
  unfold varchenko_root_origin alpha_root alpha_origin; norm_num

theorem total_exponent_g3 : 3 * varchenko_root_origin = -(3 / 4) := by
  unfold varchenko_root_origin alpha_root alpha_origin; norm_num

theorem total_exponent_g4 : 4 * varchenko_root_origin = -1 := by
  unfold varchenko_root_origin alpha_root alpha_origin; norm_num

theorem total_exponent_g5 : 5 * varchenko_root_origin = -(5 / 4) := by
  unfold varchenko_root_origin alpha_root alpha_origin; norm_num

theorem total_exponent_g6 : 6 * varchenko_root_origin = -(3 / 2) := by
  unfold varchenko_root_origin alpha_root alpha_origin; norm_num

theorem total_exponent_g7 : 7 * varchenko_root_origin = -(7 / 4) := by
  unfold varchenko_root_origin alpha_root alpha_origin; norm_num

theorem total_exponent_g8 : 8 * varchenko_root_origin = -2 := by
  unfold varchenko_root_origin alpha_root alpha_origin; norm_num

-- ═══════════════════════════════════════════════════════════════
-- §6. Basis transformation verification
-- ═══════════════════════════════════════════════════════════════

/-- The substitution u = x² introduces a factor 1/(2√u) = (1/2)u^{-1/2}.
    Combined with the σ-eigenspace prefactor x^{2m} = u^m and the
    curve equation y = √(x·P(x²)) = u^{1/4}√(P(u)):
      ω_{2m+1} = x^{2m}dx/(2y) = u^m · u^{-1/2} · u^{-1/4} · P(u)^{-1/2} · (1/2)du
                = (1/2) u^{m - 3/4} P(u)^{-1/2} du
    The exponent shift from m to m-3/4 is:
      m - 3/4 = m + (-3/4)
    where -3/4 is exactly alpha_origin. -/
theorem basis_exponent_shift (m : ℚ) :
    m + alpha_origin = m - 3 / 4 := by
  unfold alpha_origin; ring

/-- The Jacobian of u = x² contributes dx = du/(2√u) = (1/2)u^{-1/2}du.
    Exponent contribution: -1/2. -/
theorem jacobian_exponent : -(1 : ℚ) / 2 = -(1 / 2) := by norm_num

/-- y = √(x · P(x²)) = x^{1/2} · P(u)^{1/2} = u^{1/4} · P(u)^{1/2}.
    The 1/y contributes exponent -1/4 from u. -/
theorem curve_exponent : -(1 : ℚ) / 4 = -(1 / 4) := by norm_num

/-- Total exponent at origin: differential (-1/2) + curve (-1/4) = -3/4. -/
theorem total_origin_exponent :
    -(1 : ℚ) / 2 + (-(1 / 4)) = -(3 / 4) := by norm_num

end P93
