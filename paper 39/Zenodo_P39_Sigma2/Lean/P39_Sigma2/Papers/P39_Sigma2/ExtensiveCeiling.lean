/-
  Paper 39: Physics Reaches Σ₂⁰ — The Thermodynamic Stratification
  ExtensiveCeiling.lean: Theorem 4 — The Exact Zero-Test Theorem

  CORRECTED: The old version claimed extensive observables cap at LPO.
  This was WRONG. Counterexample: x_n = 1/n is decreasing, all terms
  positive, but the limit is 0. Knowing "∃ n, x_n > 0" says nothing
  about the limit's sign.

  CORRECT STATEMENT: The exact zero-test for ANY decreasing non-negative
  sequence (extensive or intensive) is Σ₂⁰-complete, requiring LPO_jump.

  ℓ > 0  ↔  ∃ m > 0, ∀ n, x_n ≥ 1/m     (Σ₂⁰)
  ℓ = 0  ↔  ∀ m > 0, ∃ n, x_n < 1/m      (Π₂⁰)

  The double-quantifier structure is exactly what LPO_jump decides.
  LPO (single quantifier) does NOT suffice.

  KEY INSIGHT: The bifurcation is NOT extensive vs intensive.
  BOTH types have Σ₂⁰ exact zero-tests. What collapses Σ₂⁰ → Σ₁⁰
  is the promise gap (Theorem 3), not the thermodynamic scaling.
-/
import Papers.P39_Sigma2.Defs

noncomputable section

-- ============================================================
-- Fekete's Lemma / BMC connection (still correct)
-- ============================================================

-- Bridge lemma: subadditive sequences have limits via BMC
-- (This imports the result of Paper 29: BMC ↔ LPO)
-- NOTE: Limit EXISTENCE is LPO. The sign TEST is Σ₂⁰ (LPO_jump).
axiom bmc_from_subadditive
    (f : ℕ → ℝ) (h_sub : ∀ m n, f (m + n) ≤ f m + f n) :
    LPO → ∃ L : ℝ, ∀ ε > 0, ∃ N, ∀ n, n ≥ N → |f n / (n : ℝ) - L| < ε

-- Every extensive observable's limit exists under LPO
-- (This is correct — Fekete/BMC guarantees convergence)
theorem extensive_limit_exists (O : ExtensiveObservable) :
    LPO → ∃ L : ℝ, ∀ ε > 0, ∃ N, ∀ n, n ≥ N →
      |O.finite_value n / (n : ℝ) - L| < ε := by
  intro lpo
  exact bmc_from_subadditive O.finite_value O.subadditive lpo

-- ============================================================
-- Theorem 4: The Exact Zero-Test Theorem
-- ============================================================

-- The exact zero-test for a decreasing non-negative sequence
-- has Σ₂⁰ quantifier structure:
--   "Is the limit > 0?"  ↔  ∃ m > 0, ∀ n, x_n ≥ 1/m
-- Deciding this for all such sequences requires LPO_jump.

-- Bridge axiom: deciding the exact zero-test for all
-- decreasing sequences requires LPO_jump
-- (By Σ₂⁰-completeness of the Finiteness Problem:
-- the modified Cubitt encoding produces decreasing gap sequences
-- whose zero-test reduces to FIN)
axiom exact_zero_test_requires_lpo_jump :
    (∀ s : DecreasingSeqWithLimit,
      exact_limit_positive s ∨ exact_limit_zero s) →
    LPO_jump

-- Bridge axiom: LPO_jump suffices for all exact zero-tests
-- (LPO_jump decides all Σ₂⁰ predicates, and
-- exact_limit_positive is Σ₂⁰)
axiom lpo_jump_decides_exact_zero_test :
    LPO_jump → ∀ s : DecreasingSeqWithLimit,
      exact_limit_positive s ∨ exact_limit_zero s

-- THEOREM 4 (combined): Exact zero-test ↔ LPO_jump
theorem exact_zero_test_iff_lpo_jump :
    (∀ s : DecreasingSeqWithLimit,
      exact_limit_positive s ∨ exact_limit_zero s) ↔
    LPO_jump :=
  ⟨exact_zero_test_requires_lpo_jump, lpo_jump_decides_exact_zero_test⟩

-- ============================================================
-- Why x_n = 1/n defeats the old argument
-- ============================================================

-- The old paper claimed: for subadditive f, if ∃ n, f(n)/n > 0
-- then the limit is positive. WRONG.
--
-- Counterexample: f(n) = 1 (constant) is subadditive.
-- f(n)/n = 1/n > 0 for all n, but lim f(n)/n = 0.
--
-- More generally: x_n = 1/n is decreasing, all terms positive,
-- but converges to 0. Knowing "∃ n, x_n > 0" is Σ₁⁰ and tells
-- you NOTHING about the limit. The limit test ℓ > 0 requires
-- the Σ₂⁰ witness ∃ m, ∀ n, x_n ≥ 1/m.

-- ============================================================
-- The correct picture: limit existence vs limit sign
-- ============================================================

-- LIMIT EXISTENCE: For subadditive sequences, Fekete/BMC
-- guarantees convergence under LPO. This is correct (Paper 29).
--
-- LIMIT SIGN: For ANY decreasing sequence, deciding ℓ > 0 vs
-- ℓ = 0 requires LPO_jump. This is the Σ₂⁰ zero-test.
--
-- The old paper conflated these two operations.
-- Existence is Σ₁⁰ (LPO). The sign test is Σ₂⁰ (LPO_jump).

end
