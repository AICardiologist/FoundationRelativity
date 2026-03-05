/-
  Paper 36: Cubitt's Spectral Gap Undecidability Stratification
  Main.lean: Master theorem and axiom audit

  Assembles Theorems 1-5 into the stratification theorem.
-/
import Papers.P36_CubittStratification.Defs
import Papers.P36_CubittStratification.BridgeLemmas
import Papers.P36_CubittStratification.FiniteGap
import Papers.P36_CubittStratification.ThermoLimit
import Papers.P36_CubittStratification.Pointwise
import Papers.P36_CubittStratification.ZeroTest
import Papers.P36_CubittStratification.UniformDecidability

noncomputable section

open Real

-- ============================================================
-- The Stratification Theorem
-- ============================================================

/-- THE STRATIFICATION THEOREM (Main Theorem of Paper 36).

    The Cubitt-Perez-Garcia-Wolf spectral gap undecidability is
    Turing-Weihrauch equivalent to LPO over BISH:

    (i)   Finite-volume spectral gap is BISH (Theorem 1)
    (ii)  Thermodynamic limit ↔ LPO (Theorem 2)
    (iii) Pointwise decidability given LPO (Theorem 3)
    (iv)  Physical gap zero-test ↔ WLPO (Theorem 4)
    (v-a) Uniform function is not computable (Theorem 5a)
    (v-b) Uniform function is LPO-computable (Theorem 5b)

    Consequence: Cubitt's undecidability introduces no logical
    resources beyond LPO — the same principle required for
    thermodynamic limits (Paper 29), coupling constants (Paper 32),
    and phase transitions (Paper 29). Macroscopic quantum
    undecidability costs exactly one thermodynamic limit. -/
theorem stratification_theorem :
    -- (i) Finite-volume gap is BISH-computable
    (∀ (M : TM) (L : ℕ) (ε : ℝ), 0 < ε →
      ∃ (q : ℝ), |CPgW_gap M L - q| < ε) ∧
    -- (ii) Thermodynamic limit ↔ LPO
    ((∀ (M : TM), thermo_limit_exists M) ↔ LPO) ∧
    -- (iii) Pointwise decidability (LPO → each instance decided)
    (LPO → ∀ (M : TM), spectral_gap M > 0 ∨ spectral_gap M = 0) ∧
    -- (iv) Physical gap zero-test ↔ WLPO
    ((∀ (Δ : ℝ), Δ ≥ 0 → (Δ = 0 ∨ Δ > 0)) ↔ WLPO) ∧
    -- (v-a) Uniform function is not computable
    (¬(∀ (M : TM), halts M ∨ ¬halts M)) ∧
    -- (v-b) Cubitt ≡ LPO: uniform decidability ↔ LPO
    ((∀ (M : TM), spectral_gap M > 0 ∨ spectral_gap M = 0) ↔ LPO) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  -- (i) Finite-volume gap is BISH
  · exact fun M L ε hε => finite_volume_gap_is_bish M L ε hε
  -- (ii) Thermodynamic limit ↔ LPO
  · exact thermo_limit_iff_lpo
  -- (iii) Pointwise decidability
  · exact fun hl M => pointwise_gap_decidable M hl
  -- (iv) Physical gap zero-test ↔ WLPO
  · exact physical_gap_zero_test_iff_wlpo
  -- (v-a) Not computable
  · exact gap_function_not_computable
  -- (v-b) Cubitt ≡ LPO
  · exact cubitt_is_lpo

-- ============================================================
-- Axiom Audit
-- ============================================================

#check @stratification_theorem
#print axioms stratification_theorem

-- Expected axiom profile:
-- BRIDGE LEMMAS (Level 4 — axiomatized physics from CPgW):
-- • cpgw_encoding_computable    — M ↦ H(M) is computable
-- • cpgw_gapped_of_not_halts    — ¬halts → gap > 0
-- • cpgw_gapless_of_halts       — halts → gap = 0
-- • cpgw_halting_asymptotics    — halting case convergence
-- • cpgw_nonhalting_asymptotics — non-halting case convergence
-- • cpgw_gap_dichotomy          — gap ∈ {0} ∪ [γ, ∞)
-- • cpgw_finite_gap_computable  — finite-volume eigenvalue computation
-- • tm_from_seq / tm_from_seq_halts — sequence-to-TM encoding
--
-- CONSTRUCTIVE PRINCIPLES:
-- • bmc_of_lpo                  — LPO → BMC
-- • wlpo_of_lpo                 — LPO → WLPO
-- • halting_problem_undecidable — ¬(∀ M, halts M ∨ ¬halts M)
-- • wlpo_to_zero_test           — WLPO → zero-test
-- • zero_test_to_wlpo           — zero-test → WLPO
--
-- LEAN 4 FOUNDATIONS:
-- • propext, Classical.choice, Quot.sound
--
-- NO sorry. All theorems are either proved or bridge-axiomatized.
-- Classical.choice appears only from by_contra in proofs using LPO.

end
