/-
  CRMLint — Case Studies: Closing Three Conservation Gaps
  Paper 76 of the Constructive Reverse Mathematics Series

  Three Mathlib theorems about ℕ (statement cost: BISH) whose proofs
  route through classical axioms (proof cost: CLASS). We provide
  constructive replacements that eliminate the classical dependency.

  Case 1: coprime_or_dvd_of_prime  — Mathlib uses `apply em`
  Case 2: coprime_of_dvd           — Mathlib uses `by_contra`
  Case 3: not_prime_iff_exists_mul_eq — Mathlib uses `Classical.not_not`

  Each replacement achieves the same result without Classical.em,
  Classical.byContradiction, or Classical.not_not, using only
  constructive machinery already present in Mathlib (Irreducible,
  DecidableEq ℕ, minFac).

  Author: Paul C.-K. Lee
  Date: February 2026
-/
import CRMLint
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs

open Nat

-- ============================================================
-- § 1. Case Study 1: coprime_or_dvd_of_prime
-- ============================================================
-- Original (Mathlib, Data/Nat/Prime/Basic.lean:202):
--   theorem coprime_or_dvd_of_prime {p} (pp : Prime p)
--       (i : ℕ) : Coprime p i ∨ p ∣ i := by
--     rw [pp.dvd_iff_not_coprime]; apply em
--
-- Classical axiom: Classical.em (Excluded Middle)
-- CRMLint diagnosis: CLASS proof, BISH statement, Δ = 3 levels
--
-- Constructive fix: gcd(p, i) divides p; since p is irreducible,
-- gcd(p, i) = 1 ∨ gcd(p, i) = p. No Excluded Middle needed.

theorem coprime_or_dvd_of_prime_constructive {p} (pp : Nat.Prime p)
    (i : ℕ) : Nat.Coprime p i ∨ p ∣ i := by
  rcases pp.eq_one_or_self_of_dvd (Nat.gcd p i) (Nat.gcd_dvd_left p i) with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [← h]; exact Nat.gcd_dvd_right p i)

-- Verify: no Classical.choice in the proof
#print axioms coprime_or_dvd_of_prime_constructive

-- ============================================================
-- § 2. Case Study 2: coprime_of_dvd
-- ============================================================
-- Original (Mathlib, Data/Nat/Prime/Defs.lean:405):
--   theorem coprime_of_dvd {m n : ℕ}
--       (H : ∀ k, Prime k → k ∣ m → ¬k ∣ n) : Coprime m n := by
--     rw [coprime_iff_gcd_eq_one]
--     by_contra g2
--     obtain ⟨p, hp, hpdvd⟩ := exists_prime_and_dvd g2
--     apply H p hp <;> apply dvd_trans hpdvd
--     · exact gcd_dvd_left _ _
--     · exact gcd_dvd_right _ _
--
-- Classical axiom: Classical.byContradiction (via by_contra)
-- CRMLint diagnosis: CLASS proof, BISH statement, Δ = 3 levels
--
-- Constructive fix: replace by_contra with by_cases on
-- DecidableEq ℕ (gcd m n = 1 is decidable).

theorem coprime_of_dvd_constructive {m n : ℕ}
    (H : ∀ k, Nat.Prime k → k ∣ m → ¬k ∣ n) : Nat.Coprime m n := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_cases g : Nat.gcd m n = 1
  · exact g
  · exact absurd ((Nat.minFac_dvd (Nat.gcd m n)).trans (Nat.gcd_dvd_right m n))
      (H _ (Nat.minFac_prime g) ((Nat.minFac_dvd (Nat.gcd m n)).trans (Nat.gcd_dvd_left m n)))

-- Verify: no Classical.choice in the proof
#print axioms coprime_of_dvd_constructive

-- ============================================================
-- § 3. Case Study 3: not_prime_iff_exists_mul_eq
-- ============================================================
-- Original (Mathlib, Data/Nat/Prime/Basic.lean:85):
--   theorem not_prime_iff_exists_mul_eq {n : ℕ} (h : 2 ≤ n) :
--       ¬Prime n ↔ ∃ a b, a < n ∧ b < n ∧ a * b = n := by
--     rw [prime_iff_not_exists_mul_eq, and_iff_right h, Classical.not_not]
--
-- Classical axiom: Classical.not_not (double negation elimination)
-- CRMLint diagnosis: CLASS proof, BISH statement, Δ = 3 levels
--
-- Constructive fix: forward direction uses minFac to produce
-- explicit witnesses instead of eliminating ¬¬∃.

theorem not_prime_iff_exists_mul_eq_constructive {n : ℕ} (h : 2 ≤ n) :
    ¬Nat.Prime n ↔ ∃ a b, a < n ∧ b < n ∧ a * b = n := by
  constructor
  · -- Forward: produce explicit witnesses via minFac
    intro np
    have hne : n ≠ 1 := by omega
    have hlt := (Nat.not_prime_iff_minFac_lt h).mp np
    have hdvd := Nat.minFac_dvd n
    have hprime := Nat.minFac_prime hne
    refine ⟨n.minFac, n / n.minFac, hlt, ?_, ?_⟩
    · exact Nat.div_lt_self (by omega) hprime.one_lt
    · exact Nat.mul_div_cancel' hdvd
  · -- Reverse: non-trivial factorisation → not prime
    intro ⟨a, b, ha, hb, hab⟩
    have ha1 : a ≠ 1 := by
      intro h1; rw [h1, one_mul] at hab; omega
    have hb1 : b ≠ 1 := by
      intro h1; rw [h1, mul_one] at hab; omega
    rw [← hab]
    exact Nat.not_prime_mul ha1 hb1

-- Verify: no Classical.choice in the proof
#print axioms not_prime_iff_exists_mul_eq_constructive

-- ============================================================
-- § 4. CRMLint audit of the case study theorems
-- ============================================================

-- Audit the Mathlib originals (should show CLASS):
#crm_audit Nat.coprime_or_dvd_of_prime
#crm_audit Nat.coprime_of_dvd

-- Audit our constructive replacements (should show BISH):
#crm_audit coprime_or_dvd_of_prime_constructive
#crm_audit coprime_of_dvd_constructive
#crm_audit not_prime_iff_exists_mul_eq_constructive
