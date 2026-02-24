/-
  Paper 59 — Module 1: Defs
  De Rham Decidability — The p-adic Precision Bound

  Core structures for elliptic curve data and good reduction data.
  All computation is integer arithmetic: no p-adic analysis or period rings.

  Sorry budget: 0.

  Paul C.-K. Lee, February 2026
-/
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Prime.Basic

/-! # Core Definitions

The p-adic precision bound for BISH-decidable verification is:

    N_M = v_p(det(1 - φ)) = v_p(1 - a_p + p)

where a_p = Tr(φ) is the trace of Frobenius and p is a prime of good reduction.

The beautiful arithmetic identity: det(1 - φ) = #E(𝔽_p), the number of
𝔽_p-rational points on the reduction. So the precision bound equals the
p-adic valuation of the point count.
-/

namespace P59

/-- An elliptic curve over ℚ, represented by minimal Weierstrass data. -/
structure EllipticCurveData where
  /-- Cremona label (e.g., "11a1", "37a1"). -/
  label : String
  /-- Conductor of the curve. -/
  conductor : ℕ
  /-- The conductor is positive. -/
  conductor_pos : conductor > 0

/-- Good reduction data at a prime p.

For an elliptic curve E/ℚ with good reduction at p, the crystalline
Frobenius φ on D_cris(V_p(E)) has characteristic polynomial
T² - a_p·T + p, where a_p is the trace of Frobenius.

The Hasse bound |a_p| ≤ 2√p is encoded in squared form to avoid
irrational numbers: a_p² ≤ 4p. -/
structure GoodReductionData where
  /-- The underlying elliptic curve. -/
  curve : EllipticCurveData
  /-- The prime of good reduction. -/
  p : ℕ
  /-- Primality of p. -/
  p_prime : Nat.Prime p
  /-- Trace of Frobenius a_p. -/
  a_p : ℤ
  /-- The Hasse bound in squared form: |a_p| ≤ 2√p ↔ a_p² ≤ 4p. -/
  hasse_bound : a_p ^ 2 ≤ 4 * (p : ℤ)

/-- The characteristic polynomial det(T - φ) evaluated at T = 1:
    det(1 - φ) = 1 - a_p + p = #E(𝔽_p). -/
def det_one_minus_frob (d : GoodReductionData) : ℤ :=
  1 - d.a_p + d.p

/-- Reduction type classification for good reduction primes. -/
inductive ReductionType where
  /-- Good ordinary reduction: v_p(a_p) = 0 (i.e., p does not divide a_p). -/
  | ordinary
  /-- Good supersingular reduction: a_p = 0 (for p ≥ 5; for p = 2,3 may have a_p ≠ 0). -/
  | supersingular
  /-- Generic good reduction (neither ordinary nor supersingular in the strict sense). -/
  | generic
  deriving Repr, BEq, DecidableEq

end P59
