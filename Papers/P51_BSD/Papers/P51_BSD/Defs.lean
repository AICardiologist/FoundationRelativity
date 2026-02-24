/-
  Paper 51: The Constructive Archimedean Rescue in BSD
  Defs.lean — Core definitions

  Defines the minimal data structures for the BSD formalization:
  - ECData: elliptic curve invariants needed for height bounds
  - RatPoint: rational point representation for height computation
  - naiveHeight: logarithmic Weil height h(P) = log max(|p|, |q|)

  Mathlib's WeierstrassCurve provides discriminant and j-invariant,
  but has no height functions, L-functions, or Mordell-Weil rank.
  We define lightweight self-contained structures following the
  Paper 28 HOParams pattern.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Papers.P51

-- ========================================================================
-- Elliptic Curve Data (lightweight, self-contained)
-- ========================================================================

/-- Minimal data for an elliptic curve E/ℚ needed for the BSD argument.
    We do not use Mathlib's full WeierstrassCurve machinery because
    Mathlib has no height theory. Instead we package exactly the
    invariants that enter the Silverman bound and the search space
    construction. -/
structure ECData where
  /-- The conductor N of E/ℚ. -/
  N : ℕ
  hN : 0 < N
  /-- Log of absolute value of j-invariant: log|j(E)|. -/
  log_j : ℝ
  /-- Log of absolute value of minimal discriminant: log|Δ_min|. -/
  log_Delta : ℝ
  /-- Silverman's computable constant μ(E) bounding |ĥ(P) − ½h(P)|.
      From Silverman (1990, AEC Theorem VIII.9.3):
        μ(E) = ⅛·log|j| + 1/12·log|Δ| + 0.973
      This is a deterministic function of the curve data. -/
  mu : ℝ
  /-- The mu constant is non-negative (it bounds an absolute value). -/
  hmu : 0 ≤ mu

-- ========================================================================
-- Rational Points
-- ========================================================================

/-- A rational point on E, represented by its projective x-coordinate
    as p/q in lowest terms. The y-coordinate is determined (up to sign)
    by the Weierstrass equation; for height purposes only x matters.

    For the identity (point at infinity), this representation is not
    needed since the identity has canonical height 0 and is torsion. -/
structure RatPoint where
  /-- Numerator of x-coordinate in lowest terms. -/
  p : ℤ
  /-- Denominator of x-coordinate in lowest terms. -/
  q : ℤ
  /-- The denominator is nonzero. -/
  hq : q ≠ 0

-- ========================================================================
-- Naive (Weil) Height
-- ========================================================================

/-- Naive (logarithmic Weil) height of a rational point.
    h(P) = log max(|p|, |q|) where x(P) = p/q in lowest terms.
    This is the standard definition from Silverman AEC Ch. VIII.

    Since q ≠ 0, we have |q| ≥ 1, so max(|p|, |q|) ≥ 1,
    guaranteeing h(P) ≥ 0. -/
noncomputable def naiveHeight (P : RatPoint) : ℝ :=
  Real.log (max (|P.p| : ℝ) (|P.q| : ℝ))

/-- The naive height is non-negative.
    Proof: q ≠ 0 implies |q| ≥ 1 implies max(|p|, |q|) ≥ 1
    implies log(max(|p|, |q|)) ≥ 0. -/
theorem naiveHeight_nonneg (P : RatPoint) : 0 ≤ naiveHeight P := by
  simp only [naiveHeight]
  apply Real.log_nonneg
  have hq_abs : (1 : ℤ) ≤ |P.q| := Int.one_le_abs P.hq
  have : (1 : ℝ) ≤ (|P.q| : ℝ) := by exact_mod_cast hq_abs
  linarith [le_max_right (|P.p| : ℝ) (|P.q| : ℝ)]

end Papers.P51
