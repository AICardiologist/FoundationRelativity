/-
  Paper 74: Forward Direction — Algebraic Spectrum → BISH Eigenvalues

  This is the content of Paper 45, reviewed here for completeness.
  When Frobenius eigenvalues are algebraic (geometric origin, Deligne),
  testing |α| = q^{w/2} is exact algebraic arithmetic → BISH.

  The mechanism (Paper 45 Theorem C1):
    α ∈ Q̄  ⟹  |α|² = αᾱ  (product of conjugates, algebraic)
    q^{w/2} algebraic  ⟹  |α|² = q^w  is algebraic identity
    → decidable by finite GCD computation → BISH

  References: Paper 45 Theorem C1, Deligne (1974, 1980).
-/
import Papers.P74_Axiom2Reverse.Defs

open CRMLevel SpectrumType

-- ============================================================
-- Forward: Algebraic Spectrum → BISH Eigenvalues
-- ============================================================

/-- With algebraic spectrum (geometric origin), eigenvalue
    decidability is BISH. Algebraic number arithmetic is
    computable: minimal polynomial comparison is finite. -/
theorem algebraic_gives_BISH :
    eigenvalue_cost algebraic = BISH := by
  unfold eigenvalue_cost
  exact algebraic_eigenvalue_cost_eq

/-- Without algebraic spectrum (continuous Langlands parameters),
    eigenvalue decidability requires WLPO. Testing whether a
    continuous spectral parameter equals an algebraic value
    is a real-number equality test. -/
theorem continuous_gives_WLPO :
    eigenvalue_cost continuous = WLPO := by
  unfold eigenvalue_cost
  exact continuous_eigenvalue_cost_eq
