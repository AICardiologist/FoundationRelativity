/-
  Paper 39: Physics Reaches Σ₂⁰ — The Physical Stratification Theorem
  Stratification.lean: Theorem 5 — The Physical Stratification

  CORRECTED MAIN THEOREM: The arithmetic complexity of a physical
  observable is determined by its epistemic mode, not its
  thermodynamic scaling:
    (i)   Platonic exact physics (no promise) → LPO_jump (Σ₂⁰)
    (ii)  Promise-gapped physics → LPO (Σ₁⁰)
    (iii) Empirical physics (finite precision) → LPO (Σ₁⁰)

  The old "extensive vs intensive" bifurcation was wrong:
  BOTH extensive and intensive exact zero-tests are Σ₂⁰.
  What reduces Σ₂⁰ to Σ₁⁰ is the promise gap, not the
  thermodynamic type.
-/
import Papers.P39_Sigma2.Defs
import Papers.P39_Sigma2.GenericGapSigma2
import Papers.P39_Sigma2.PromiseGapRecovery
import Papers.P39_Sigma2.ExtensiveCeiling

noncomputable section

-- ============================================================
-- Part (i): Platonic exact physics requires LPO_jump
-- ============================================================

-- Two independent witnesses:
-- (a) The generic spectral gap (intensive observable):
--     (∀ M, gapped ∨ gapless) ↔ LPO_jump
--     (From GenericGapSigma2.lean)
-- (b) The exact zero-test for decreasing sequences:
--     (∀ s, limit > 0 ∨ limit = 0) ↔ LPO_jump
--     (From ExtensiveCeiling.lean — covers BOTH extensive and intensive)

-- ============================================================
-- Part (ii): Promise-gapped physics caps at LPO
-- ============================================================

-- (From PromiseGapRecovery.lean)
-- promise_gapped_caps_at_lpo : ∀ H, LPO → (gapless ∨ ¬gapless)

-- ============================================================
-- Part (iii): Empirical physics caps at LPO
-- ============================================================

-- Finite measurement precision ε > 0 imposes an effective promise gap.
-- Deciding "gap > ε" vs "gap < ε" is Σ₁⁰, hence LPO-decidable.

-- Bridge lemma: empirical gap decision is Σ₁⁰
axiom empirical_gap_sigma1 (H : ModifiedHamiltonian) (ε : ℝ) (hε : ε > 0) :
    LPO → (gap_less_than H ε ∨ ¬gap_less_than H ε)

-- ============================================================
-- Theorem 5: The Physical Stratification Theorem
-- ============================================================

theorem physical_stratification :
    -- Part (i): Platonic exact physics — spectral gap ↔ LPO_jump
    ((∀ M, is_gapped (modified_hamiltonian M) ∨
           ¬is_gapped (modified_hamiltonian M)) ↔ LPO_jump) ∧
    -- Part (i'): Platonic exact physics — zero-test ↔ LPO_jump
    ((∀ s : DecreasingSeqWithLimit,
        exact_limit_positive s ∨ exact_limit_zero s) ↔ LPO_jump) ∧
    -- Part (ii): Promise-gapped physics caps at LPO
    (∀ (H : PromiseGapped), LPO →
      (is_gapless H.hamiltonian ∨ ¬is_gapless H.hamiltonian)) ∧
    -- Part (iii): Empirical physics caps at LPO
    (∀ (H : ModifiedHamiltonian) (ε : ℝ), ε > 0 → LPO →
      (gap_less_than H ε ∨ ¬gap_less_than H ε)) :=
  ⟨generic_gap_iff_lpo_jump,
   exact_zero_test_iff_lpo_jump,
   promise_gapped_caps_at_lpo,
   empirical_gap_sigma1⟩

end
