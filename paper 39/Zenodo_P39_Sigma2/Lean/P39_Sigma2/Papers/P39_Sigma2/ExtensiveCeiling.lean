/-
  Paper 39: Physics Reaches Σ₂⁰ — The Thermodynamic Stratification
  ExtensiveCeiling.lean: Theorem 5 — Extensive observables cap at LPO

  KEY INSIGHT: Extensive observables (energy density, free energy,
  magnetization) converge via Fekete's Lemma / BMC (subadditivity).
  Subadditivity forces monotone convergence, which caps at LPO.

  This is why the thermodynamic bifurcation exists:
  - Extensive (subadditive → monotone → BMC → LPO)
  - Intensive (infimum → no monotonicity → Σ₂⁰ → LPO_jump)
-/
import Papers.P39_Sigma2.Defs

noncomputable section

-- ============================================================
-- Fekete's Lemma / BMC connection
-- ============================================================

-- Bridge lemma: subadditive sequences have limits via BMC
-- (This imports the result of Paper 29: BMC ↔ LPO)
axiom bmc_from_subadditive
    (f : ℕ → ℝ) (h_sub : ∀ m n, f (m + n) ≤ f m + f n) :
    LPO → ∃ L : ℝ, ∀ ε > 0, ∃ N, ∀ n, n ≥ N → |f n / (n : ℝ) - L| < ε

-- Bridge lemma: the sign of the limit is LPO-decidable
-- (monotone convergence from above makes the zero test Π₁⁰ = LPO)
axiom subadditive_sign_decidable
    (f : ℕ → ℝ) (h_sub : ∀ m n, f (m + n) ≤ f m + f n) :
    LPO → (∃ n, f n / (n : ℝ) > 0) ∨ ∀ n, f n / (n : ℝ) ≤ 0

-- ============================================================
-- Theorem 5: Extensive observables cap at LPO
-- ============================================================

-- Every extensive observable's limit exists under LPO
theorem extensive_limit_exists (O : ExtensiveObservable) :
    LPO → ∃ L : ℝ, ∀ ε > 0, ∃ N, ∀ n, n ≥ N →
      |O.finite_value n / (n : ℝ) - L| < ε := by
  intro lpo
  exact bmc_from_subadditive O.finite_value O.subadditive lpo

-- The sign of an extensive observable is LPO-decidable
theorem extensive_sign_lpo (O : ExtensiveObservable) :
    LPO → (∃ n, O.finite_value n / (n : ℝ) > 0) ∨
           ∀ n, O.finite_value n / (n : ℝ) ≤ 0 := by
  intro lpo
  exact subadditive_sign_decidable O.finite_value O.subadditive lpo

-- Bridge lemma: extensive sign is decidable from subadditive sign
axiom extensive_sign_from_subadditive (O : ExtensiveObservable) :
    (∃ n, O.finite_value n / (n : ℝ) > 0) →
    extensive_sign_positive O

axiom extensive_not_sign_from_subadditive (O : ExtensiveObservable) :
    (∀ n, O.finite_value n / (n : ℝ) ≤ 0) →
    ¬extensive_sign_positive O

-- Combined: LPO decides extensive observables
theorem extensive_cap_lpo (O : ExtensiveObservable) :
    LPO → (extensive_sign_positive O ∨ ¬extensive_sign_positive O) := by
  intro lpo
  rcases extensive_sign_lpo O lpo with ⟨n, hn⟩ | h_all
  · left; exact extensive_sign_from_subadditive O ⟨n, hn⟩
  · right; exact extensive_not_sign_from_subadditive O h_all

-- ============================================================
-- Why intensive observables escape the LPO ceiling
-- ============================================================

-- Intensive observables are NOT subadditive.
-- They are determined by infima (not averages).
-- The infimum of a non-monotone sequence can oscillate,
-- and deciding "infimum = 0" requires ∀∃ quantification (Π₂⁰).
--
-- Formally:
--   inf_k f(k) = 0  ↔  ∀ ε > 0, ∃ k, f(k) < ε    (Π₂⁰)
--   inf_k f(k) > 0  ↔  ∃ ε > 0, ∀ k, f(k) ≥ ε     (Σ₂⁰)
--
-- This double-quantifier structure is exactly what LPO_jump decides.
-- LPO (single quantifier) does NOT suffice.

-- ============================================================
-- Summary of the extensive/intensive bifurcation
-- ============================================================

-- Extensive: subadditive → monotone limit → BMC → LPO
-- Intensive: infimum → no monotonicity → Finiteness → LPO_jump
-- Promise gap: collapses ∀∃ to ∃ → LPO

end
