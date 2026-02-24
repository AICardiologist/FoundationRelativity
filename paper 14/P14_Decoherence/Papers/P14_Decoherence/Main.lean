/-
Papers/P14_Decoherence/Main.lean
Paper 14: The Measurement Problem as a Logical Artefact.

Assembly module: imports all components and runs axiom audits.

Results summary:

PART A (BISH content — Level 0):
  • coherence_eq_geometric: c(N) = |ρ₀ 0 1| · |cos(θ/2)|^N
  • decoherence_epsilon_bound: ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, c(N) < ε
  • coherence_antitone: c is non-increasing
  • decoherenceMap_trace: trace preservation
  • decoherenceMap_eq_physical: explicit formula = Tr_E[U·(ρ⊗|0⟩⟨0|)·U†]

  Axiom profile: propext, Quot.sound (standard Mathlib infrastructure).
  No omniscience principles. Pure BISH.

PART B (LPO equivalence — Level 1):
  • exact_decoherence_iff_LPO: ABC ↔ LPO
  • coherence_is_antitone_bounded: coherence is an instance of ABC

  Axiom profile: adds bmc_of_lpo, lpo_of_bmc (axiomatized, cited from
  Bridges–Vîță 2006 and Paper 8 respectively).

Three physical domains, one logical structure (BMC ↔ LPO):
  | Domain             | Bounded Monotone Sequence | LPO Content          |
  |---------------------|---------------------------|----------------------|
  | Stat. Mech. (P8)    | Free energy f_N          | f_∞ exists exactly   |
  | Gen. Rel. (P13)     | Radial coordinate r(τ)   | r → 0 exactly        |
  | Quantum Meas. (P14) | Coherence c(N)           | c → 0 (collapse)     |
-/
import Papers.P14_Decoherence.ExactDecoherence

namespace Papers.P14

-- ========================================================================
-- Part A: BISH content (axiom audit)
-- ========================================================================

section BISH

#check @coherence_eq_geometric
#check @decoherence_epsilon_bound
#check @coherence_antitone
#check @coherence_nonneg
#check @decoherenceMap_trace
#check @decoherenceMap_eq_physical

-- Axiom certificates: should show only propext, Quot.sound
-- (standard Mathlib infrastructure; no omniscience principles)
#print axioms coherence_eq_geometric
#print axioms decoherence_epsilon_bound
#print axioms coherence_antitone
#print axioms coherence_nonneg
#print axioms decoherenceMap_trace
#print axioms decoherenceMap_eq_physical
#print axioms coherence_zero_of_diagonal

end BISH

-- ========================================================================
-- Part B: LPO equivalence (axiom audit)
-- ========================================================================

section LPO_Equivalence

#check @exact_decoherence_iff_LPO
#check @abc_iff_bmc
#check @lpo_iff_bmc
#check @coherence_is_antitone_bounded

-- Axiom certificates: should show bmc_of_lpo, lpo_of_bmc in addition
-- to standard Mathlib axioms
#print axioms exact_decoherence_iff_LPO
#print axioms abc_iff_bmc
#print axioms lpo_iff_bmc

end LPO_Equivalence

-- ========================================================================
-- Supporting lemmas (axiom audit)
-- ========================================================================

section Supporting

#print axioms decoherence_iterate_offdiag
#print axioms decoherence_iterate_00
#print axioms decoherence_iterate_11
#print axioms generalCoherenceProduct_antitone
#print axioms abs_cos_half_lt_one

end Supporting

end Papers.P14
