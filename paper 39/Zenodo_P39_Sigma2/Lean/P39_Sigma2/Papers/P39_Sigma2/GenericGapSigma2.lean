/-
  Paper 39: Physics Reaches Σ₂⁰ — The Thermodynamic Stratification
  GenericGapSigma2.lean: Theorem 2 — Generic spectral gap is Σ₂⁰-complete

  THE MAIN NEW RESULT: Without a promise gap, deciding "gapped vs. gapless"
  for a generic translation-invariant Hamiltonian requires LPO_jump (Σ₂⁰-LEM),
  strictly stronger than LPO (Σ₁⁰-LEM).
-/
import Papers.P39_Sigma2.Defs
import Papers.P39_Sigma2.ArithmeticHierarchy
import Papers.P39_Sigma2.ModifiedEncoding

noncomputable section

-- ============================================================
-- Step 1: Gap decision ↔ Finiteness decision
-- ============================================================

-- Deciding "is gapped" for all modified Hamiltonians is equivalent
-- to deciding the Finiteness Problem for all TMs
theorem gap_iff_finiteness :
    (∀ M, is_gapped (modified_hamiltonian M) ∨
          ¬is_gapped (modified_hamiltonian M)) ↔
    (∀ M, finiteness_problem M ∨ ¬finiteness_problem M) := by
  constructor
  · intro h_dec M
    rcases h_dec M with h_gap | h_not_gap
    · left; exact (modified_gapped_iff_finite M).mp h_gap
    · right; intro h_fin
      exact h_not_gap ((modified_gapped_iff_finite M).mpr h_fin)
  · intro h_dec M
    rcases h_dec M with h_fin | h_inf
    · left; exact (modified_gapped_iff_finite M).mpr h_fin
    · right; intro h_gap
      exact h_inf ((modified_gapped_iff_finite M).mp h_gap)

-- ============================================================
-- Step 2: Finiteness requires LPO_jump
-- ============================================================

-- From ArithmeticHierarchy.lean: finiteness_is_sigma2_complete
-- The Finiteness Problem is Σ₂⁰-complete, so deciding it for
-- all TMs requires LPO_jump.

-- ============================================================
-- Theorem 2a: Generic gap decision requires LPO_jump
-- ============================================================

theorem generic_gap_requires_lpo_jump :
    (∀ M, is_gapped (modified_hamiltonian M) ∨
          ¬is_gapped (modified_hamiltonian M)) →
    LPO_jump := by
  intro h_dec
  exact sigma2_complete_implies_lpo_jump
    (gap_iff_finiteness.mp h_dec)
    finiteness_is_sigma2_complete

-- ============================================================
-- Theorem 2b: LPO_jump suffices for generic gap decision
-- ============================================================

theorem lpo_jump_decides_generic_gap :
    LPO_jump →
    (∀ M, is_gapped (modified_hamiltonian M) ∨
          ¬is_gapped (modified_hamiltonian M)) := by
  intro lpo_j
  exact gap_iff_finiteness.mpr
    (lpo_jump_decides_sigma2 lpo_j finiteness_is_sigma2_complete)

-- ============================================================
-- Theorem 2 (combined): Generic gap ↔ LPO_jump
-- ============================================================

theorem generic_gap_iff_lpo_jump :
    (∀ M, is_gapped (modified_hamiltonian M) ∨
          ¬is_gapped (modified_hamiltonian M)) ↔
    LPO_jump :=
  ⟨generic_gap_requires_lpo_jump, lpo_jump_decides_generic_gap⟩

-- ============================================================
-- Corollary: Generic gapless decision is also LPO_jump
-- ============================================================

theorem generic_gapless_iff_lpo_jump :
    (∀ M, is_gapless (modified_hamiltonian M) ∨
          ¬is_gapless (modified_hamiltonian M)) ↔
    LPO_jump := by
  constructor
  · intro h_dec
    apply generic_gap_requires_lpo_jump
    intro M
    rcases h_dec M with h_gl | h_ngl
    · right
      intro h_g
      exact ((gapped_iff_not_gapless _).mp h_g) h_gl
    · left
      exact (gapped_iff_not_gapless _).mpr h_ngl
  · intro lpo_j M
    rcases lpo_jump_decides_generic_gap lpo_j M with h_g | h_ng
    · right
      exact (gapped_iff_not_gapless _).mp h_g
    · left
      by_contra h_ngl
      exact h_ng ((gapped_iff_not_gapless _).mpr h_ngl)

end
