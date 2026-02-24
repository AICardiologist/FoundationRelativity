/-
  Paper 59 — Module 2: PadicVal
  De Rham Decidability — The p-adic Precision Bound

  Divisibility-based valuation helpers.
  The p-adic valuation v_p(n) is characterized by:
    p^k | n  and  ¬ p^(k+1) | n

  We avoid Mathlib's noncomputable `padicValNat`/`padicValInt` and instead
  use direct divisibility proofs closed by `omega` and `norm_num`.

  Sorry budget: 0.

  Paul C.-K. Lee, February 2026
-/
import Papers.P59_DeRhamDecidability.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace P59

/-! # Valuation Certificates

A valuation certificate for v_p(n) = k consists of two parts:
1. p^k divides n
2. p^(k+1) does not divide n

For the verification table, each entry provides these two facts directly.
-/

/-- A valuation certificate: v_p(n) = k, witnessed by divisibility. -/
structure ValuationCert (p : ℕ) (n : ℤ) (k : ℕ) : Prop where
  /-- p^k divides n. -/
  pow_dvd : (p : ℤ) ^ k ∣ n
  /-- p^(k+1) does not divide n. -/
  pow_succ_not_dvd : ¬ (p : ℤ) ^ (k + 1) ∣ n

/-- When p does not divide n, the valuation is 0. -/
theorem val_zero_of_not_dvd {p : ℕ} {n : ℤ} (h : ¬ (p : ℤ) ∣ n) :
    ValuationCert p n 0 where
  pow_dvd := ⟨n, by simp⟩
  pow_succ_not_dvd := by simpa using h

/-- Helper: the determinant computation 1 - a_p + p. -/
theorem det_computation (a_p : ℤ) (p : ℕ) :
    1 - a_p + (p : ℤ) = (1 + p : ℤ) - a_p := by ring

/-- The point count #E(𝔽_p) = 1 - a_p + p is always an integer.
    This is trivial since a_p ∈ ℤ and p ∈ ℕ ⊂ ℤ, but worth stating
    for conceptual clarity. -/
theorem point_count_integer (a_p : ℤ) (p : ℕ) :
    ∃ n : ℤ, n = 1 - a_p + (p : ℤ) := ⟨1 - a_p + p, rfl⟩

end P59
