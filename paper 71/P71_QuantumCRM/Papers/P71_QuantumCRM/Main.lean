/-
  Paper 71 — Engineering Consequences of the Archimedean Principle
  Main.lean: Root module + axiom audit

  Summary: 4 engineering applications of the Archimedean Principle
  I.   Archimedean Security (lattice crypto resists Shor)
  II.  Approximate SVP Phase Transition (LLL vs BKZ)
  III. Conjugacy Design Principle (Kyber > NTRU > RSA)
  IV.  Eigendecomposition Integrality (algebraic-direct vs eigendecompose+round)

  Build: lake build → 0 errors, 0 warnings, 0 sorry
-/
import Papers.P71_QuantumCRM.Defs
import Papers.P71_QuantumCRM.Problems
import Papers.P71_QuantumCRM.Security
import Papers.P71_QuantumCRM.Integrality

-- ============================================================
-- Axiom audit: all main theorems
-- ============================================================

-- Theorem I: Archimedean Security
#check @archimedean_security
#check @svp_hardness_is_archimedean
#check @svp_archimedean_collapse
#check @post_quantum_transition_justified

-- Theorem II: Approximate SVP Phase Transition
#check @svp_phase_transition
#check @transition_is_descent_boundary
#check @exact_equals_polynomial_crm
#check @nist_in_metric_regime

-- Theorem III: Conjugacy Design Principle
#check @kyber_beats_ntru_beats_rsa
#check @conjugacy_security_ordering

-- Theorem IV: Eigendecomposition Integrality
#check @eigendecomposition_integrality
#check @integrality_gap
#check @lll_vs_pca

-- Assembly
#check @full_classification
#check @three_and_three

-- Foundation: Defs
#check @mp_gap
#check @projection_strictly_stronger
#check @metric_targets_block_shor
#check @algebraic_targets_enable_shor
#check @target_types_distinct
#check @security_monotone
#check @continuous_dominates_discrete
#check @spectral_delocalization
#check @crypto_dimension_misalignment

-- Integrality: sum-of-squares lemma
#check @Fin.sum_eq_one_iff
#check @int_sq_sum_one

-- Print axioms for main theorems
#print axioms archimedean_security
#print axioms svp_phase_transition
#print axioms conjugacy_security_ordering
#print axioms eigendecomposition_integrality
#print axioms post_quantum_transition_justified
#print axioms full_classification
#print axioms int_sq_sum_one
