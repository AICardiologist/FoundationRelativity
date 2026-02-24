/-
  Paper 71 — Engineering Consequences of the Archimedean Principle
  Problems.lean: Cryptographic problem profiles, crypto scheme profiles,
                 approximate SVP regimes, algorithm types, quantum algorithm profiles
-/
import Papers.P71_QuantumCRM.Defs

-- ============================================================
-- Section 1: Cryptographic Problem Profiles
-- ============================================================

/-- A cryptographic/computational problem, classified by CRM. -/
structure ProblemProfile where
  name            : String
  target_type     : TargetType
  has_archimedean : Bool
  crm_level       : CRMLevel
  descent_type    : DescentType
  deriving Repr

/-- Integer factorization (RSA security).
    Algebraic target: period of f(x) = aˣ mod N in (ℤ/Nℤ)×.
    Shor converts search → projection via QFT on cyclic group. -/
def factoring : ProblemProfile where
  name            := "Integer Factoring"
  target_type     := .algebraic
  has_archimedean := false
  crm_level       := .BISH_MP
  descent_type    := .search

/-- Discrete logarithm (ECC security).
    Algebraic target: exponent k with g^k = h. -/
def dlog : ProblemProfile where
  name            := "Discrete Logarithm"
  target_type     := .algebraic
  has_archimedean := false
  crm_level       := .BISH_MP
  descent_type    := .search

/-- SVP over ℤ-lattices in ℝⁿ.
    Metric target: shortest vector by Euclidean norm.
    Gram eigenbasis projection destroys integrality → BDD → MP search. -/
def svp_integers : ProblemProfile where
  name            := "SVP over ℤ-lattice"
  target_type     := .metric
  has_archimedean := true
  crm_level       := .BISH_MP
  descent_type    := .search

/-- SVP over function field lattices.
    No Archimedean place → polynomial-time (Lenstra 1985) → BISH. -/
def svp_function_field : ProblemProfile where
  name            := "SVP over 𝔽_q[t]-lattice"
  target_type     := .algebraic  -- Ultrametric = algebraic over function fields
  has_archimedean := false
  crm_level       := .BISH
  descent_type    := .projection

/-- LWE: metric target (recover secret from noisy inner products). -/
def lwe : ProblemProfile where
  name            := "LWE"
  target_type     := .metric
  has_archimedean := true
  crm_level       := .BISH_MP
  descent_type    := .search

/-- Ring-LWE over ℤ_q[x]/(xⁿ+1).
    Has NTT (spectral decomposition), but error target is metric.
    NTT and Euclidean shortness are canonically conjugate. -/
def ring_lwe : ProblemProfile where
  name            := "Ring-LWE"
  target_type     := .metric
  has_archimedean := true
  crm_level       := .BISH_MP
  descent_type    := .search

-- ============================================================
-- Section 2: Cryptographic Scheme Profiles (with Conjugacy)
-- ============================================================

/-- A cryptographic scheme, classified by conjugacy level. -/
structure CryptoSchemeProfile where
  name      : String
  target    : TargetType
  conjugacy : ConjugacyLevel
  crm_level : CRMLevel
  deriving Repr

/-- ML-KEM (Kyber): cyclotomic NTT, Gaussian errors → flat spectrum.
    Maximally conjugate. -/
def kyber : CryptoSchemeProfile where
  name      := "ML-KEM (Kyber)"
  target    := .metric
  conjugacy := .maximal
  crm_level := .BISH_MP

/-- NTRU: xⁿ−1 has trivial character, partial spectral localization. -/
def ntru : CryptoSchemeProfile where
  name      := "NTRU"
  target    := .metric
  conjugacy := .intermediate
  crm_level := .BISH_MP

/-- RSA: algebraic period → spectral peak → Shor extracts. -/
def rsa_scheme : CryptoSchemeProfile where
  name      := "RSA"
  target    := .algebraic
  conjugacy := .minimal
  crm_level := .BISH_MP

-- ============================================================
-- Section 3: Approximate SVP Regimes
-- ============================================================

/-- Approximation regime for lattice reduction.
    The CRM framework identifies a hard boundary between
    projection-descent (LLL, exponential γ) and
    search-descent (BKZ, polynomial γ). -/
inductive ApproxRegime : Type where
  | exponential : ApproxRegime  -- γ = 2^{O(n)}, LLL achieves this
  | polynomial  : ApproxRegime  -- γ = poly(n), requires BKZ-type
  | exact       : ApproxRegime  -- γ = 1, exact shortest vector
  deriving DecidableEq, Repr

/-- CRM level of each approximation regime. -/
def regime_crm_level (r : ApproxRegime) : CRMLevel :=
  match r with
  | .exponential => .BISH      -- LLL: algebraic projection, polynomial time
  | .polynomial  => .BISH_MP   -- BKZ: metric search on sublattice blocks
  | .exact       => .BISH_MP   -- Full search over ℤⁿ

/-- Descent type of each approximation regime. -/
def regime_descent (r : ApproxRegime) : DescentType :=
  match r with
  | .exponential => .projection  -- LLL works by algebraic inner products
  | .polynomial  => .search      -- BKZ block-searches reintroduce MP
  | .exact       => .search      -- Full lattice search

-- ============================================================
-- Section 4: Algorithm Types (Eigendecomposition Integrality)
-- ============================================================

/-- Whether an algorithm stage involves eigendecomposition
    followed by discretization (the integrality-destroying operation). -/
inductive AlgorithmType : Type where
  | algebraic_direct     : AlgorithmType  -- Works on integers (LLL, HNF, SNF)
  | eigendecompose_round : AlgorithmType  -- Eigendecompose then round (PCA, spectral clustering)
  deriving DecidableEq, Repr

/-- CRM level of each algorithm type. -/
def algorithm_crm (a : AlgorithmType) : CRMLevel :=
  match a with
  | .algebraic_direct     => .BISH      -- No transcendental contamination
  | .eigendecompose_round => .BISH_MP   -- Rounding = BDD = MP search

/-- Descent type of each algorithm type. -/
def algorithm_descent (a : AlgorithmType) : DescentType :=
  match a with
  | .algebraic_direct     => .projection
  | .eigendecompose_round => .search

/-- A numerical algorithm, classified by CRM. -/
structure NumericalAlgorithm where
  name      : String
  alg_type  : AlgorithmType
  crm_level : CRMLevel
  deriving Repr

def lll_alg : NumericalAlgorithm where
  name      := "LLL lattice reduction"
  alg_type  := .algebraic_direct
  crm_level := .BISH

def hnf_alg : NumericalAlgorithm where
  name      := "Hermite Normal Form"
  alg_type  := .algebraic_direct
  crm_level := .BISH

def snf_alg : NumericalAlgorithm where
  name      := "Smith Normal Form"
  alg_type  := .algebraic_direct
  crm_level := .BISH

def pca_round : NumericalAlgorithm where
  name      := "PCA + rounding"
  alg_type  := .eigendecompose_round
  crm_level := .BISH_MP

def spectral_cluster : NumericalAlgorithm where
  name      := "Spectral clustering + assignment"
  alg_type  := .eigendecompose_round
  crm_level := .BISH_MP

-- ============================================================
-- Section 5: Quantum Algorithm Profiles (warm-up from §2)
-- ============================================================

/-- A quantum algorithm stage. -/
structure AlgorithmStage where
  name      : String
  crm_level : CRMLevel
  descent   : DescentType
  deriving Repr

/-- Projection-native: all stages are projection-descent. -/
def isProjectionNative (stages : List AlgorithmStage) : Bool :=
  stages.all (fun s => s.descent == .projection)

/-- MP residual: at least one stage is search-descent. -/
def hasMPResidual (stages : List AlgorithmStage) : Bool :=
  stages.any (fun s => s.descent == .search)

def shor_stages : List AlgorithmStage :=
  [ ⟨"Classical reduction", .BISH, .projection⟩,
    ⟨"State preparation", .BISH, .projection⟩,
    ⟨"Modular exponentiation", .BISH, .projection⟩,
    ⟨"QFT", .BISH, .projection⟩,
    ⟨"Measurement", .BISH, .projection⟩ ]

def grover_stages : List AlgorithmStage :=
  [ ⟨"State preparation", .BISH, .projection⟩,
    ⟨"Oracle query", .BISH_MP, .search⟩,
    ⟨"Diffusion", .BISH, .projection⟩,
    ⟨"Measurement", .BISH, .projection⟩ ]

def qpe_stages : List AlgorithmStage :=
  [ ⟨"Ancilla preparation", .BISH, .projection⟩,
    ⟨"Controlled unitaries", .BISH, .projection⟩,
    ⟨"Inverse QFT", .BISH, .projection⟩,
    ⟨"Measurement", .BISH, .projection⟩ ]

def qsim_stages : List AlgorithmStage :=
  [ ⟨"State preparation", .BISH, .projection⟩,
    ⟨"Trotterized evolution", .BISH, .projection⟩,
    ⟨"Observable measurement", .BISH, .projection⟩ ]
