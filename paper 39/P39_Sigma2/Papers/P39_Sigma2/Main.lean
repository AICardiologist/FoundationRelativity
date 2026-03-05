/-
  Paper 39: Physics Reaches Σ₂⁰ — The Physical Stratification
  Main.lean: Master theorem and axiom audit

  Physics reaches Σ₂⁰. The spectral gap of a generic
  translation-invariant Hamiltonian (without promise gap)
  is Σ₂⁰-complete, requiring LPO_jump — the Turing jump of LPO.

  CORRECTED: The bifurcation is platonic exact vs promise-gapped,
  NOT extensive vs intensive. Both types of exact zero-tests
  are Σ₂⁰. The promise gap (or finite precision) collapses Σ₂⁰ → Σ₁⁰.
-/
import Papers.P39_Sigma2.Stratification

noncomputable section

-- ============================================================
-- Stratification Table (CORRECTED)
-- ============================================================

structure StratificationEntry where
  name : String
  epistemic_mode : String  -- "exact" | "promise-gapped" | "empirical"
  logical_principle : String  -- "LPO" | "LPO_jump"
  arithmetic_level : String  -- "Sigma1" | "Sigma2"
  deriving Repr

def stratification_table : List StratificationEntry := [
  -- Platonic exact physics (no promise gap) → LPO_jump
  ⟨"Spectral gap (generic, no promise)", "exact", "LPO_jump", "Sigma2"⟩,
  ⟨"Energy density limit sign (exact)", "exact", "LPO_jump", "Sigma2"⟩,
  ⟨"Correlation length (exact)", "exact", "LPO_jump", "Sigma2"⟩,
  -- Promise-gapped physics → LPO
  ⟨"Spectral gap (Cubitt promise)", "promise-gapped", "LPO", "Sigma1"⟩,
  ⟨"Phase diagram (BCW promise)", "promise-gapped", "LPO", "Sigma1"⟩,
  ⟨"Wang tiling (Paper 38)", "promise-gapped", "LPO", "Sigma1"⟩,
  -- Empirical physics (finite precision) → LPO
  ⟨"Any observable (finite ε)", "empirical", "LPO", "Sigma1"⟩
]

-- All exact entries are LPO_jump; all promise/empirical entries are LPO
theorem exact_physics_is_lpo_jump :
    ∀ e ∈ stratification_table,
      e.epistemic_mode = "exact" →
      e.logical_principle = "LPO_jump" := by
  intro e he h_mode
  simp [stratification_table] at he
  rcases he with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩
  all_goals (first | rfl | (simp at h_mode))

theorem promise_empirical_is_lpo :
    ∀ e ∈ stratification_table,
      e.epistemic_mode = "promise-gapped" ∨ e.epistemic_mode = "empirical" →
      e.logical_principle = "LPO" := by
  intro e he h_mode
  simp [stratification_table] at he
  rcases he with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩
  all_goals (first | rfl | (simp at h_mode))

-- ============================================================
-- Master Theorem (CORRECTED)
-- ============================================================

/-- MASTER THEOREM: The Physical Stratification of Undecidability.

    Part 1 (Exact ceiling): Generic spectral gap ↔ LPO_jump.
    Part 2 (Zero-test): Exact zero-test for decreasing sequences ↔ LPO_jump.
    Part 3 (Promise recovery): Promise-gapped physics caps at LPO.
    Part 4 (Empirical ceiling): Empirical (finite-precision) physics caps at LPO.

    PUNCHLINE: The arithmetic complexity of a physical observable is
    determined by its epistemic mode (exact vs promise-gapped vs empirical),
    NOT by its thermodynamic scaling (extensive vs intensive).
    - Exact platonic physics → LPO_jump (Σ₂⁰)
    - Promise gap collapses Σ₂⁰ → Σ₁⁰ (LPO)
    - Finite precision collapses Σ₂⁰ → Σ₁⁰ (LPO) -/
theorem sigma2_master :
    -- Part 1: Generic spectral gap ↔ LPO_jump
    ((∀ M, is_gapped (modified_hamiltonian M) ∨
           ¬is_gapped (modified_hamiltonian M)) ↔ LPO_jump) ∧
    -- Part 2: Exact zero-test ↔ LPO_jump
    ((∀ s : DecreasingSeqWithLimit,
        exact_limit_positive s ∨ exact_limit_zero s) ↔ LPO_jump) ∧
    -- Part 3: Promise-gapped cap at LPO
    (∀ (H : PromiseGapped), LPO →
      (is_gapless H.hamiltonian ∨ ¬is_gapless H.hamiltonian)) ∧
    -- Part 4: Empirical cap at LPO
    (∀ (H : ModifiedHamiltonian) (ε : ℝ), ε > 0 → LPO →
      (gap_less_than H ε ∨ ¬gap_less_than H ε)) :=
  physical_stratification

-- ============================================================
-- Axiom Audit (CORRECTED)
-- ============================================================

-- Bridge lemmas (physics):
-- 1. modified_hamiltonian (modified Cubitt encoding)
-- 2. modified_gapped_iff_finite (gapped ↔ finite halting set)
-- 3. modified_gapless_iff_infinite (gapless ↔ infinite halting set)
-- 4. gapped_iff_not_gapless (complementarity)
-- 5. finiteness_is_sigma2_complete (Σ₂⁰-completeness of FIN)
-- 6. bmc_from_subadditive (Fekete/BMC limit existence — LPO)
-- 7. exact_zero_test_requires_lpo_jump (zero-test → LPO_jump)
-- 8. lpo_jump_decides_exact_zero_test (LPO_jump → zero-test)
-- 9. promise_gap_sigma1_test (promise → Σ₁⁰)
-- 10. empirical_gap_sigma1 (empirical → Σ₁⁰)
-- 11. tm_from_seq, tm_from_seq_halts (TM encoding)
-- Plus Lean infrastructure: propext, Classical.choice, Quot.sound
--
-- REMOVED (v2 correction):
-- subadditive_sign_decidable — FALSE axiom (1/n counterexample)
-- extensive_sign_from_subadditive, extensive_not_sign_from_subadditive
-- extensive_sign_positive, extensive_cap_lpo

#print axioms sigma2_master

end
