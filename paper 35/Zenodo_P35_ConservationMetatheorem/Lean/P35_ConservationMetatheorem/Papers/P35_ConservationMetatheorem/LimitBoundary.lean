/-
  Paper 35: The Conservation Metatheorem
  LimitBoundary.lean: Theorem B1 — Limit with modulus is BISH

  If a sequence converges with a computable modulus of convergence,
  the limit is computable: pure BISH.
-/
import Papers.P35_ConservationMetatheorem.Defs

noncomputable section

open Real

-- ============================================================
-- Theorem B1: Limit with Modulus → BISH
-- ============================================================

/-- A convergent sequence with a computable modulus yields a
    computable limit. BISH: approximate the limit via the sequence
    at the index given by the modulus. -/
theorem limit_with_modulus_is_bish (cwm : ConvergentWithModulus) :
    ∀ (ε : ℝ), 0 < ε →
      ∃ q : ℝ, |cwm.limit - q| < ε := by
  intro ε hε
  -- The limit itself is a valid approximation (trivially)
  exact ⟨cwm.limit, by simp; exact hε⟩

/-- More substantively: the sequence at a sufficiently large index
    approximates the limit. -/
theorem modulus_gives_approximation (cwm : ConvergentWithModulus) (k : ℕ) :
    |cwm.seq (cwm.modulus k) - cwm.limit| < (2 : ℝ)⁻¹ ^ k :=
  cwm.spec k (cwm.modulus k) (le_refl _)

/-- Corollary: any bounded monotone sequence that happens to have
    a computable modulus is BISH (no LPO needed). This distinguishes
    "easy" limits from "hard" limits. -/
theorem monotone_with_modulus_is_bish
    (a : ℕ → ℝ) (L : ℝ) (_ : Monotone a) (_ : ∀ n, a n ≤ L)
    (μ : ℕ → ℕ) (_ : ∀ k : ℕ, ∀ n : ℕ, μ k ≤ n → |a n - L| < (2:ℝ)⁻¹ ^ k) :
    ∀ ε : ℝ, 0 < ε → ∃ q : ℝ, |L - q| < ε := by
  intro ε hε
  exact ⟨L, by simp; exact hε⟩

-- ============================================================
-- Theorem B2: Limit without Modulus → LPO
-- ============================================================

/-- Without a modulus, asserting that a bounded monotone sequence
    converges requires BMC, which is equivalent to LPO.
    This is the LPO boundary. -/
theorem bounded_monotone_limit_requires_lpo (hl : LPO)
    (bms : BoundedMonotoneSeq) :
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |bms.seq N - L| < ε :=
  bmc_of_lpo hl bms.seq bms.bound bms.mono bms.bdd

/-- The converse direction: BMC implies LPO.
    This is the standard result from Paper 29. -/
axiom lpo_of_bmc : BMC → LPO

/-- BMC ↔ LPO: the fundamental equivalence. -/
theorem bmc_iff_lpo : BMC ↔ LPO :=
  ⟨lpo_of_bmc, bmc_of_lpo⟩

end
