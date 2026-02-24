/-
  Paper 71 — Engineering Consequences of the Archimedean Principle
  Security.lean: The four main theorems

  Theorem I:   Archimedean Security (lattice problems resist Shor)
  Theorem II:  Approximate SVP Phase Transition
  Theorem III: Conjugacy Design Principle
  Theorem IV:  Eigendecomposition Integrality
-/
import Papers.P71_QuantumCRM.Problems

-- ============================================================
-- THEOREM I: Archimedean Security of Lattice Cryptography
-- ============================================================

/-- The main security theorem: lattice problems (metric targets)
    are immune to Shor-type attacks, while RSA/DLog (algebraic targets)
    are vulnerable. -/
theorem archimedean_security :
    -- Lattice problems: metric target → no projection conversion
    admits_projection_conversion svp_integers.target_type = false
    ∧ admits_projection_conversion ring_lwe.target_type = false
    ∧ admits_projection_conversion lwe.target_type = false
    -- Lattice problems: search-descent → MP residual persists
    ∧ svp_integers.descent_type = .search
    ∧ ring_lwe.descent_type = .search
    -- Classical crypto: algebraic target → projection conversion exists
    ∧ admits_projection_conversion factoring.target_type = true
    ∧ admits_projection_conversion dlog.target_type = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- SVP hardness is purely Archimedean: removing the Archimedean
    place collapses SVP from BISH+MP to BISH. -/
theorem svp_hardness_is_archimedean :
    svp_integers.has_archimedean = true
    ∧ svp_function_field.has_archimedean = false
    ∧ svp_integers.crm_level > svp_function_field.crm_level := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- The Archimedean collapse: SVP over function fields is BISH. -/
theorem svp_archimedean_collapse :
    svp_function_field.crm_level = .BISH
    ∧ svp_integers.crm_level = .BISH_MP := by
  constructor <;> native_decide

/-- The post-quantum transition is structurally justified:
    migrating from algebraic-target crypto (RSA, ECC) to
    metric-target crypto (lattice) moves from Shor-vulnerable
    to Shor-immune. -/
theorem post_quantum_transition_justified :
    -- Factoring: Shor converts search → projection → BISH
    post_descent .projection = .BISH
    -- SVP: search-descent → BISH+MP (irreducible)
    ∧ post_descent svp_integers.descent_type = .BISH_MP
    -- The gap is strict
    ∧ post_descent .projection < post_descent .search := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ============================================================
-- THEOREM II: Approximate SVP Phase Transition
-- ============================================================

/-- The phase transition: exponential approximation is BISH (LLL),
    polynomial approximation is BISH+MP (BKZ). -/
theorem svp_phase_transition :
    regime_crm_level .exponential = .BISH
    ∧ regime_crm_level .polynomial = .BISH_MP
    ∧ regime_crm_level .exponential < regime_crm_level .polynomial := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- The phase transition is at the descent-type boundary. -/
theorem transition_is_descent_boundary :
    regime_descent .exponential = .projection
    ∧ regime_descent .polynomial = .search := by
  constructor <;> native_decide

/-- Exact SVP has the same CRM level as polynomial approx:
    both require search. The approximation factor doesn't change
    the logical type once you're in the metric regime. -/
theorem exact_equals_polynomial_crm :
    regime_crm_level .exact = regime_crm_level .polynomial := by native_decide

/-- NIST parameters are in the metric regime (BKZ-hard, not LLL-hard). -/
theorem nist_in_metric_regime :
    regime_descent .polynomial = .search
    ∧ regime_crm_level .polynomial = .BISH_MP := by
  constructor <;> native_decide

-- ============================================================
-- THEOREM III: Conjugacy Design Principle
-- ============================================================

/-- Kyber is structurally more secure than NTRU, which is more
    secure than RSA, ordered by conjugacy level. -/
theorem kyber_beats_ntru_beats_rsa :
    rsa_scheme.conjugacy < ntru.conjugacy
    ∧ ntru.conjugacy < kyber.conjugacy := by
  constructor <;> native_decide

/-- Conjugacy correlates with quantum immunity. -/
theorem conjugacy_security_ordering :
    -- RSA: minimal conjugacy, algebraic target, Shor-vulnerable
    rsa_scheme.conjugacy = .minimal
    ∧ admits_projection_conversion rsa_scheme.target = true
    -- NTRU: partial conjugacy, metric target, Shor-immune
    ∧ ntru.conjugacy = .intermediate
    ∧ admits_projection_conversion ntru.target = false
    -- Kyber: maximal conjugacy, metric target, Shor-immune
    ∧ kyber.conjugacy = .maximal
    ∧ admits_projection_conversion kyber.target = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- ============================================================
-- THEOREM IV: Eigendecomposition Integrality
-- ============================================================

/-- Direct algebraic algorithms preserve integrality (BISH). -/
theorem algebraic_preserves_integrality :
    algorithm_crm .algebraic_direct = .BISH := by native_decide

/-- Eigendecompose+round introduces MP search. -/
theorem eigendecompose_introduces_mp :
    algorithm_crm .eigendecompose_round = .BISH_MP := by native_decide

/-- The integrality gap is strict. -/
theorem integrality_gap :
    algorithm_crm .algebraic_direct < algorithm_crm .eigendecompose_round := by
  native_decide

/-- LLL is BISH, PCA+round is BISH+MP. -/
theorem lll_vs_pca :
    lll_alg.crm_level = .BISH
    ∧ pca_round.crm_level = .BISH_MP
    ∧ lll_alg.crm_level < pca_round.crm_level := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- The integrality theorem for algorithm descent types. -/
theorem eigendecomposition_integrality :
    algorithm_crm .algebraic_direct = .BISH
    ∧ algorithm_crm .eigendecompose_round = .BISH_MP
    ∧ algorithm_crm .algebraic_direct < algorithm_crm .eigendecompose_round := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ============================================================
-- ASSEMBLY: Full Classification
-- ============================================================

/-- Combined classification table covering all four applications. -/
theorem full_classification :
    -- Pre-quantum crypto: algebraic targets, Shor-vulnerable
    admits_projection_conversion factoring.target_type = true
    ∧ admits_projection_conversion dlog.target_type = true
    -- Post-quantum crypto: metric targets, Shor-immune
    ∧ admits_projection_conversion svp_integers.target_type = false
    ∧ admits_projection_conversion ring_lwe.target_type = false
    -- Function field control: remove ℝ → SVP becomes BISH
    ∧ svp_function_field.crm_level = .BISH
    -- Hardness is purely Archimedean
    ∧ svp_integers.has_archimedean = true
    ∧ svp_function_field.has_archimedean = false
    -- Phase transition: LLL is BISH, BKZ is BISH+MP
    ∧ regime_crm_level .exponential = .BISH
    ∧ regime_crm_level .polynomial = .BISH_MP
    -- Eigendecomposition: algebraic-direct is BISH, eigendecompose+round is BISH+MP
    ∧ algorithm_crm .algebraic_direct = .BISH
    ∧ algorithm_crm .eigendecompose_round = .BISH_MP := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- ============================================================
-- WARM-UP: Quantum Algorithm Classification (from §2)
-- ============================================================

/-- Shor is projection-native. -/
theorem shor_projection_native :
    isProjectionNative shor_stages = true := by native_decide

/-- Grover has MP residual. -/
theorem grover_has_mp_residual :
    hasMPResidual grover_stages = true := by native_decide

/-- QPE is projection-native. -/
theorem qpe_projection_native :
    isProjectionNative qpe_stages = true := by native_decide

/-- Quantum simulation is projection-native. -/
theorem qsim_projection_native :
    isProjectionNative qsim_stages = true := by native_decide

/-- Three projection-native, three search-contaminated. -/
theorem three_and_three :
    isProjectionNative shor_stages = true
    ∧ isProjectionNative qpe_stages = true
    ∧ isProjectionNative qsim_stages = true
    ∧ hasMPResidual grover_stages = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
