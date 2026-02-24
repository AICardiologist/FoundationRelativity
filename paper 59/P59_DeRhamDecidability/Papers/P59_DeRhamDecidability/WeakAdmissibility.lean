/-
  Paper 59 — Module 4: WeakAdmissibility
  De Rham Decidability — The p-adic Precision Bound

  The abstract theorem: the Hasse bound implies #E(𝔽_p) > 0,
  so the precision bound N_M = v_p(#E(𝔽_p)) is always well-defined.

  Mathematical background:
  - For a crystalline representation V with D = D_cris(V), the key
    operator (1-φ) loses precision v_p(det(1-φ)) when inverted.
  - Weak admissibility (Colmez-Fontaine) guarantees det(1-φ) ≠ 0.
  - For elliptic curves: det(1-φ) = 1 - a_p + p = #E(𝔽_p) ≥ 1.

  Sorry budget: 0.

  Paul C.-K. Lee, February 2026
-/
import Papers.P59_DeRhamDecidability.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace P59

/-! # Hasse Bound Implies Positivity

The key theorem: from the Hasse bound a_p² ≤ 4p and p ≥ 2, we derive
that 1 - a_p + p > 0 (equivalently, #E(𝔽_p) ≥ 1).

Proof sketch: If a_p ≥ p+1, then a_p² ≥ (p+1)² = p² + 2p + 1 > 4p
(since (p-1)² > 0 for p ≥ 2). This contradicts the Hasse bound.
Therefore a_p ≤ p, and 1 - a_p + p ≥ 1 > 0.
-/

/-- **Theorem A (Hasse implies positivity).**
    From the Hasse bound a_p² ≤ 4p and p ≥ 2,
    the point count #E(𝔽_p) = 1 - a_p + p is positive.

    This is the mathematical heart of the formalization:
    weak admissibility guarantees det(1-φ) ≠ 0, and in fact det(1-φ) ≥ 1. -/
theorem hasse_implies_positive (p : ℕ) (a_p : ℤ)
    (hp : p ≥ 2) (hasse : a_p ^ 2 ≤ 4 * (p : ℤ)) :
    1 - a_p + (p : ℤ) > 0 := by
  -- If a_p ≥ p+1 then a_p² ≥ (p+1)² = (p-1)² + 4p > 4p for p ≥ 2,
  -- contradicting the Hasse bound. So a_p ≤ p, hence 1 - a_p + p ≥ 1.
  nlinarith [sq_nonneg (a_p - (p : ℤ) - 1), sq_nonneg ((p : ℤ) - 1)]

/-- The point count is also bounded below by 1 (sharper statement). -/
theorem point_count_ge_one (p : ℕ) (a_p : ℤ)
    (hp : p ≥ 2) (hasse : a_p ^ 2 ≤ 4 * (p : ℤ)) :
    1 - a_p + (p : ℤ) ≥ 1 := by
  nlinarith [sq_nonneg (a_p - (p : ℤ) - 1), sq_nonneg ((p : ℤ) - 1)]

/-- The point count is nonzero (used for well-definedness of v_p). -/
theorem point_count_ne_zero (p : ℕ) (a_p : ℤ)
    (hp : p ≥ 2) (hasse : a_p ^ 2 ≤ 4 * (p : ℤ)) :
    1 - a_p + (p : ℤ) ≠ 0 := by
  linarith [hasse_implies_positive p a_p hp hasse]

/-- Applied to GoodReductionData: det(1 - φ) > 0. -/
theorem det_pos (d : GoodReductionData) :
    det_one_minus_frob d > 0 := by
  unfold det_one_minus_frob
  exact hasse_implies_positive d.p d.a_p
    (Nat.Prime.two_le d.p_prime) d.hasse_bound

/-! # Supersingular Case: a_p = 0 implies N_M = 0

For supersingular primes with a_p = 0 (always the case for p ≥ 5):
    det(1-φ) = 1 + p
and v_p(1+p) = 0 for all p ≥ 2 (since 1 + p ≡ 1 mod p).
-/

/-- **Theorem C (Supersingular case).**
    When a_p = 0, det(1-φ) = 1 + p, and p does not divide 1 + p.
    Therefore N_M = 0: no precision loss at supersingular primes. -/
theorem supersingular_no_precision_loss (p : ℕ) (hp : p ≥ 2) :
    ¬ (p : ℤ) ∣ (1 + (p : ℤ)) := by
  rintro ⟨k, hk⟩
  -- hk : 1 + ↑p = ↑p * k, so ↑p * (k - 1) = 1
  -- Since p ≥ 2, this means p ∣ 1, which forces p ≤ 1, contradiction.
  have h1 : (p : ℤ) ∣ 1 :=
    ⟨k - 1, by linarith [mul_sub (p : ℤ) k 1]⟩
  have h2 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
  linarith [show (p : ℤ) ≥ 2 from by exact_mod_cast hp]

/-- The supersingular determinant value. -/
theorem supersingular_det (p : ℕ) :
    (1 : ℤ) - 0 + (p : ℤ) = 1 + (p : ℤ) := by simp

/-! # Ordinary Case Analysis

For good ordinary reduction, v_p(a_p) = 0 (p does not divide a_p).
The precision bound N_M = v_p(1 - a_p + p) depends on whether
p divides (1 - a_p).

- If 1 - a_p ≢ 0 mod p: since p ∣ p but p ∤ (1 - a_p),
  we get p ∤ (1 - a_p + p), so N_M = 0.
- If 1 - a_p ≡ 0 mod p: then N_M = v_p(1 - a_p + p) ≥ 1.
  These are the "anomalous" primes.
-/

/-- **Theorem B (Ordinary, non-anomalous).**
    If p does not divide (1 - a_p), then p does not divide
    (1 - a_p + p), so N_M = 0. -/
theorem ordinary_non_anomalous {p : ℕ} {a_p : ℤ}
    (_hp : Nat.Prime p) (h : ¬ (p : ℤ) ∣ (1 - a_p)) :
    ¬ (p : ℤ) ∣ (1 - a_p + (p : ℤ)) := by
  rintro ⟨k, hk⟩
  apply h
  exact ⟨k - 1, by linarith [mul_sub (p : ℤ) k 1]⟩

/-! # Upper Bound on N_M

The Hasse bound gives #E(𝔽_p) ≤ 1 + 2√p + p = (1 + √p)².
For p ≥ 5, this means #E(𝔽_p) < p², so N_M ≤ 1.
More precisely: N_M ≤ 2 for all p (since #E(𝔽_p) < p³ always).
-/

/-- The upper Hasse bound: 1 - a_p + p ≤ 1 + 2p + p.
    This is a weak bound; the tight bound uses 2√p instead of 2p.
    Still useful: guarantees the point count is at most 1 + 3p. -/
theorem point_count_upper_bound (p : ℕ) (a_p : ℤ)
    (_hp : p ≥ 2) (hasse : a_p ^ 2 ≤ 4 * (p : ℤ)) :
    1 - a_p + (p : ℤ) ≤ 1 + 2 * (p : ℤ) + (p : ℤ) := by
  -- From a_p² ≤ 4p ≤ 4p² (for p ≥ 1), we get |a_p| ≤ 2p, so -a_p ≤ 2p.
  nlinarith [sq_nonneg (a_p + (p : ℤ) + 1), sq_nonneg ((p : ℤ) - 1)]

end P59
