/-
  Paper 74: Axiom 2 Reverse Characterization — Definitions
  Algebraic Spectrum Is Necessary for BISH Eigenvalue Decidability

  Parallels Paper 72 (Axiom 3) and Paper 73 (Axiom 1).
  Paper 72: positive-definite height ↔ BISH cycle-search.
  Paper 73: Standard Conjecture D ↔ BISH morphism decidability.
  Paper 74: algebraic spectrum ↔ BISH eigenvalue decidability.

  The mathematical content:
  - With geometric origin (Deligne, Weil I/II): Frobenius eigenvalues are
    algebraic integers satisfying |α| = q^{w/2}. Testing this is exact
    algebraic arithmetic → BISH.
  - Without geometric origin (analytic Langlands parameters): the spectral
    parameters are continuous complex variables (Maass forms, unramified
    characters). Testing |α| = q^{w/2} for a continuous parameter is a
    real-number equality test → WLPO.

  Key distinction from Axioms 1 and 3: the cost is WLPO, not LPO.
  - LPO: existential search (∃n, a(n) = 1) — cycle-search, radical detection
  - WLPO: equality test (a = 0̄ ∨ a ≠ 0̄) — spectral parameter comparison
  Eigenvalue comparison is a single equality test, not a search.

  Why not "transcendental eigenvalues" (three fatal flaws):
  (1) Weil II (Deligne 1980): ALL separated schemes of finite type over F_q
      have algebraic Frobenius eigenvalues. No transcendentals in motives.
  (2) Linear algebra: if morphisms are finite-dimensional Q-vector spaces
      (Axiom 1), endomorphisms satisfy minimal polynomials → eigenvalues
      algebraic. Can't drop Axiom 2 without dropping Axiom 1.
  (3) ℓ-adic trap: mapping transcendental Q̄_ℓ elements to C requires
      Axiom of Choice → CLASS, not WLPO.

  The correct framing: Axiom 2 fails when the category accommodates the
  full analytic Langlands spectrum (not restricted to geometric origin).
  The spectral parameters live in C natively, avoiding the CLASS trap.

  References: Paper 45 (Weil eigenvalue CRM), Paper 50 (DPT axioms),
    Deligne (Weil I, 1974; Weil II, 1980), Bump (1997),
    Bridges-Richman (1987).
-/
import Mathlib.Order.Defs.PartialOrder

-- ============================================================
-- CRM Hierarchy (shared with Papers 72, 73)
-- ============================================================

inductive CRMLevel : Type where
  | BISH    : CRMLevel
  | BISH_MP : CRMLevel
  | LLPO    : CRMLevel
  | WLPO    : CRMLevel
  | LPO     : CRMLevel
  | CLASS   : CRMLevel
  deriving DecidableEq, Repr, Inhabited

open CRMLevel

def CRMLevel.toNat : CRMLevel → Nat
  | BISH    => 0
  | BISH_MP => 1
  | LLPO    => 2
  | WLPO    => 3
  | LPO     => 4
  | CLASS   => 5

instance : LE CRMLevel where
  le a b := a.toNat ≤ b.toNat

instance : LT CRMLevel where
  lt a b := a.toNat < b.toNat

instance (a b : CRMLevel) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

instance (a b : CRMLevel) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toNat < b.toNat))

-- ============================================================
-- Spectrum Type (Paper 74 specific)
-- ============================================================

/-- Classification of the Frobenius/Hecke spectrum in a motivic or
    automorphic category.

    - Algebraic: eigenvalues are algebraic numbers (geometric origin).
      Deligne (Weil I/II) proves this for all motives arising from
      algebraic geometry over finite fields. Testing |α| = q^{w/2}
      reduces to exact algebraic arithmetic → BISH.
      Reference: Deligne (1974, 1980), Paper 45 Theorem C1.

    - Continuous: spectral parameters are continuous complex variables
      without geometric origin. The full analytic Langlands spectrum
      includes Maass forms (spectral parameter s ∈ C), unramified
      characters, and representations of non-compact real groups.
      Testing whether a continuous parameter satisfies the Ramanujan
      bound is a real-number equality test → WLPO.
      Reference: Bump (1997), Paper 45 Theorem C2. -/
inductive SpectrumType : Type where
  | algebraic  : SpectrumType  -- Axiom 2 holds (geometric origin)
  | continuous : SpectrumType  -- Axiom 2 fails (analytic parameters)
  deriving DecidableEq, Repr

open SpectrumType

/-- Whether the spectrum has geometric origin (Axiom 2). -/
def is_algebraic : SpectrumType → Bool
  | algebraic  => true
  | continuous => false

-- ============================================================
-- Axiomatized Eigenvalue Costs (Paper 69/72/73 pattern)
-- ============================================================

/-- CRM cost of eigenvalue decidability with algebraic spectrum.
    Geometric origin (Deligne): Frobenius eigenvalues α are algebraic
    integers. Testing |α| = q^{w/2} reduces to:
      |α|² = αᾱ = product of algebraic conjugates
      q^w = integer
    Testing equality of algebraic numbers is decidable → BISH.

    Mechanism: algebraic number arithmetic is computable. Given
    minimal polynomials for α and q^{w/2}, equality reduces to
    checking whether their minimal polynomials share a root,
    which is a finite GCD computation.
    Reference: Paper 45 Theorem C1, Deligne (1974). -/
opaque algebraic_eigenvalue_cost : CRMLevel
axiom algebraic_eigenvalue_cost_eq : algebraic_eigenvalue_cost = BISH

/-- CRM cost of eigenvalue decidability with continuous spectrum.
    Without geometric origin, spectral parameters are continuous
    complex variables. Testing |α| = q^{w/2} for a continuous
    parameter α ∈ C is a real-number equality test.

    Why WLPO (not LPO):
    - LPO: ∃n, a(n) = 1 — existential search through a sequence
    - WLPO: a = 0̄ ∨ a ≠ 0̄ — decide whether a real equals a value
    Eigenvalue comparison is a single equality test (does this
    continuous parameter equal this algebraic value?), not a search
    through an infinite structure. This is precisely WLPO.

    Example: Maass forms for GL₂(ℝ) have spectral parameter
    s ∈ ½ + iℝ. The Ramanujan conjecture asserts Re(s) = ½.
    Testing this for a given Maass form is a real-number equality
    test → WLPO. Selberg proved Re(s) ≥ ¼ unconditionally, but
    the exact bound requires WLPO.
    Reference: Paper 45 Theorem C2, Bump (1997), Selberg (1965). -/
opaque continuous_eigenvalue_cost : CRMLevel
axiom continuous_eigenvalue_cost_eq : continuous_eigenvalue_cost = WLPO

/-- CRM cost of eigenvalue decidability as a function of spectrum type.
    Delegates to axiomatized components. -/
def eigenvalue_cost : SpectrumType → CRMLevel
  | algebraic  => algebraic_eigenvalue_cost
  | continuous => continuous_eigenvalue_cost

-- ============================================================
-- Geometric Origin
-- ============================================================

/-- A representation or motive has geometric origin if its associated
    Galois representation arises from the cohomology of an algebraic
    variety. Fontaine-Mazur (1995) conjectures that geometric origin
    is equivalent to being de Rham at all primes above ℓ.

    With geometric origin: Deligne's theorem forces the spectrum
    to be algebraic. The Weil conjectures are theorems, not axioms.

    Without geometric origin: the category accommodates the full
    analytic spectrum. The Ramanujan conjecture becomes a genuine
    open question, and its decidability costs WLPO. -/
structure SpectralCategory where
  spectrum : SpectrumType
  geometric_origin : Bool

def motives_standard : SpectralCategory :=
  ⟨algebraic, true⟩

def langlands_analytic : SpectralCategory :=
  ⟨continuous, false⟩

def langlands_with_ramanujan : SpectralCategory :=
  ⟨algebraic, false⟩  -- Ramanujan proven → algebraic, but not geometric
