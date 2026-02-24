/-
  Paper 28: Newton vs. Lagrange — Constructive Stratification of Classical Mechanics
  BISHHalf.lean — The BISH half: Euler-Lagrange equations are constructively solvable

  For the discrete harmonic oscillator with N=2 time steps, the EL equation
  dS/dq = 0 reduces to the scalar linear equation:

    (8m − k) · q = 4m · (A + B)

  Under the stability condition 8m > k (which ensures the coefficient is
  nonzero), this has a unique explicit solution:

    q* = 4m(A+B) / (8m − k)

  This is fully constructive: an explicit rational expression computed in BISH.
  No Fan Theorem, no excluded middle in the proof logic.

  Note: `Classical.choice` appears in the axiom audit because Mathlib's ℝ type
  is constructed using Cauchy sequences + Classical.choice. This is an
  infrastructure artifact shared by ALL Mathlib theorems about ℝ, including
  Paper 23's BISH results. See Paper 23 AxiomAudit.lean.

  Derivation: S(q) = m(q−A)² + m(B−q)² − (k/4)(A² + q²).
  dS/dq = 2m(q−A) − 2m(B−q) − (k/2)q = (4m − k/2)q − 2m(A+B).
  Setting dS/dq = 0 and multiplying by 2: (8m − k)q = 4m(A+B).
-/
import Papers.P28_NewtonLagrange.Defs

namespace Papers.P28

-- ========================================================================
-- Explicit EL solution
-- ========================================================================

/-- The explicit Euler-Lagrange solution for N=2 harmonic oscillator.
    q* = 4m(A+B) / (8m − k). -/
noncomputable def elSolution (p : HOParams) : ℝ :=
  4 * p.m * (p.A + p.B) / (8 * p.m - p.k)

-- ========================================================================
-- BISH: The EL equation has a unique solution
-- ========================================================================

/-- **BISH Half.** The discrete Euler-Lagrange equation for the N=2
    harmonic oscillator has a unique solution, given explicitly by
    q* = 4m(A+B)/(8m−k).

    The proof uses only algebraic manipulations (field_simp, linarith).
    The stability condition `hcfl : k < 8m` ensures the EL coefficient
    is nonzero. (This is the discrete analogue of the CFL condition.)

    No Fan Theorem appears in the proof or its axiom set.
    `Classical.choice` in the audit is a Mathlib ℝ infrastructure artifact
    (same as Paper 23's BISH results). -/
theorem el_unique_solution_N2 (p : HOParams) (hcfl : p.k < 8 * p.m) :
    ∃! q : ℝ, (8 * p.m - p.k) * q = 4 * p.m * (p.A + p.B) := by
  have hne : (8 * p.m - p.k) ≠ 0 := ne_of_gt (by linarith)
  refine ⟨elSolution p, ?_, ?_⟩
  · -- Existence: c * (a / c) = a
    simp only [elSolution]
    rw [mul_div_cancel₀ _ hne]
  · -- Uniqueness: c * q = c * q' with c ≠ 0 ⟹ q = q'
    intro q' hq'
    simp only [elSolution]
    rw [eq_div_iff hne]
    linarith

/-- The explicit solution satisfies the EL equation. -/
theorem elSolution_satisfies (p : HOParams) (hcfl : p.k < 8 * p.m) :
    (8 * p.m - p.k) * elSolution p = 4 * p.m * (p.A + p.B) := by
  simp only [elSolution]
  rw [mul_div_cancel₀ _ (ne_of_gt (by linarith : 0 < 8 * p.m - p.k))]

-- ========================================================================
-- Axiom audit (BISH verification)
-- ========================================================================

-- Output: [propext, Classical.choice, Quot.sound]
-- Classical.choice is from Mathlib's ℝ construction (Cauchy sequences),
-- not from any logical use of excluded middle or FanTheorem.
-- This matches Paper 23's BISH audit pattern exactly.
-- Key verification: NO FanTheorem hypothesis, NO custom axioms.
-- See Paper 10 §Methodology for the full discussion.
#print axioms el_unique_solution_N2
#print axioms elSolution_satisfies

end Papers.P28
