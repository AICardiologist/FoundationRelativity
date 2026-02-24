/-
  Paper 28: Newton vs. Lagrange vs. Hamilton
  HamiltonBISH.lean — The Hamiltonian formulation and Legendre transform (BISH)

  This file extends the two-way stratification to a three-way stratification
  by adding:
  1. The discrete Legendre transform: q ↦ p = 2m(q − A)
  2. Discrete Hamilton's equations for N=2
  3. Unique solution of Hamilton's equations (BISH, no FT)
  4. Invertibility of the Legendre transform (BISH bridge)

  All results are purely algebraic — the Hamiltonian formulation is at
  the same BISH level as the Euler-Lagrange equation. The variational
  principle (minimizer existence) remains the only FT-level content.

  The punchline:
    BISH:  EL equation  ←—Legendre (BISH)—→  Hamilton's equations
    FT:    Lagrangian min ∃  ←— same action —→  Hamiltonian min ∃
-/
import Papers.P28_NewtonLagrange.BISHHalf

namespace Papers.P28

noncomputable section

-- ========================================================================
-- Definitions: Discrete Legendre Transform and Hamilton's Equations
-- ========================================================================

/-- Discrete Legendre transform: maps a position q₁ to conjugate momentum.
    For the harmonic oscillator with N=2, Δt=1/2:
      p₁ = ∂₂Ld(q₀, q₁) = 2m(q₁ − A)
    where Ld is the discrete Lagrangian for the first leg. -/
def discreteMomentum (p : HOParams) (q : ℝ) : ℝ :=
  2 * p.m * (q - p.A)

/-- Inverse discrete Legendre transform: recover position from momentum.
      q₁ = p₁/(2m) + A -/
def legendreInverse (p : HOParams) (mom : ℝ) : ℝ :=
  mom / (2 * p.m) + p.A

/-- Phase space solution: the EL solution paired with its conjugate momentum. -/
def elSolutionPhaseSpace (p : HOParams) : ℝ × ℝ :=
  (elSolution p, discreteMomentum p (elSolution p))

/-- Discrete Hamilton's equation 1 for N=2:
    (q₁ − A)/Δt = p₁/m, equivalently p₁ = 2m(q₁ − A).
    This is the discrete analogue of q̇ = ∂H/∂p = p/m. -/
def satisfiesHamiltonEq1 (_p : HOParams) (q₁ mom : ℝ) : Prop :=
  mom = 2 * _p.m * (q₁ - _p.A)

/-- Discrete Hamilton's equation 2 for N=2:
    The momentum matching condition, which reduces to the EL equation
    (8m − k)q₁ = 4m(A + B). This is the discrete analogue of
    ṗ = −∂H/∂q = −kq combined with the second-leg kinematics. -/
def satisfiesHamiltonEq2 (p : HOParams) (q₁ : ℝ) : Prop :=
  (8 * p.m - p.k) * q₁ = 4 * p.m * (p.A + p.B)

-- ========================================================================
-- Legendre Transform Invertibility (BISH)
-- ========================================================================

/-- The discrete Legendre transform is left-invertible:
    legendreInverse ∘ discreteMomentum = id.
    This is pure algebra over ℝ, fully constructive. -/
theorem legendre_invertible (p : HOParams) (q : ℝ) :
    legendreInverse p (discreteMomentum p q) = q := by
  unfold legendreInverse discreteMomentum
  have hm_ne : p.m ≠ 0 := ne_of_gt p.hm
  field_simp
  ring

/-- The discrete Legendre transform is right-invertible:
    discreteMomentum ∘ legendreInverse = id.
    This is pure algebra over ℝ, fully constructive. -/
theorem legendre_invertible' (p : HOParams) (mom : ℝ) :
    discreteMomentum p (legendreInverse p mom) = mom := by
  unfold discreteMomentum legendreInverse
  have hm_ne : p.m ≠ 0 := ne_of_gt p.hm
  field_simp
  ring

-- ========================================================================
-- Hamilton's Equations Satisfied by Phase Space Solution (BISH)
-- ========================================================================

/-- The phase space solution (q*, p*) satisfies Hamilton's equation 1.
    This is immediate from the definition of discreteMomentum. -/
theorem hamilton_eq1_satisfied (p : HOParams) :
    satisfiesHamiltonEq1 p (elSolutionPhaseSpace p).1 (elSolutionPhaseSpace p).2 := by
  simp only [satisfiesHamiltonEq1, elSolutionPhaseSpace, discreteMomentum]

/-- The phase space solution satisfies Hamilton's equation 2.
    This follows from elSolution_satisfies (the EL equation). -/
theorem hamilton_eq2_satisfied (p : HOParams) (hcfl : p.k < 8 * p.m) :
    satisfiesHamiltonEq2 p (elSolutionPhaseSpace p).1 := by
  unfold satisfiesHamiltonEq2 elSolutionPhaseSpace
  exact elSolution_satisfies p hcfl

/-- Both Hamilton's equations are satisfied by the phase space solution. -/
theorem hamilton_eqs_satisfied (p : HOParams) (hcfl : p.k < 8 * p.m) :
    satisfiesHamiltonEq1 p (elSolutionPhaseSpace p).1 (elSolutionPhaseSpace p).2
    ∧ satisfiesHamiltonEq2 p (elSolutionPhaseSpace p).1 :=
  ⟨hamilton_eq1_satisfied p, hamilton_eq2_satisfied p hcfl⟩

-- ========================================================================
-- Uniqueness of Hamilton Solution (BISH)
-- ========================================================================

/-- The position component is uniquely determined by Hamilton's equation 2
    (the discrete EL equation). This repackages el_unique_solution_N2. -/
theorem hamilton_q_unique (p : HOParams) (hcfl : p.k < 8 * p.m) :
    ∃! q : ℝ, satisfiesHamiltonEq2 p q :=
  el_unique_solution_N2 p hcfl

/-- Given any position q, the momentum is uniquely determined by
    Hamilton's equation 1: p = 2m(q − A). -/
theorem hamilton_p_unique (p : HOParams) (q : ℝ) :
    ∃! mom : ℝ, satisfiesHamiltonEq1 p q mom := by
  refine ⟨2 * p.m * (q - p.A), rfl, ?_⟩
  intro mom' hmom'
  exact hmom'

/-- **Hamilton Unique Solution.** The system of discrete Hamilton's
    equations for N=2 has a unique solution: q is determined by the
    EL equation (Hamilton eq 2), and p is then determined by the
    Legendre relation (Hamilton eq 1).

    This is BISH — no Fan Theorem, no excluded middle.
    The proof is purely algebraic. -/
theorem hamilton_unique_solution (p : HOParams) (hcfl : p.k < 8 * p.m) :
    (∃! q : ℝ, satisfiesHamiltonEq2 p q)
    ∧ (∀ q : ℝ, ∃! mom : ℝ, satisfiesHamiltonEq1 p q mom) :=
  ⟨hamilton_q_unique p hcfl, hamilton_p_unique p⟩

-- ========================================================================
-- Legendre Consistency (BISH)
-- ========================================================================

/-- The Lagrangian EL solution and Hamiltonian solution are related by
    the Legendre transform. This is definitionally true — the phase
    space solution is defined via the Legendre transform of elSolution.

    Stated as a theorem because the *paper* needs to assert that the
    two formulations are connected by a BISH bridge. -/
theorem legendre_consistency (p : HOParams) :
    (elSolutionPhaseSpace p).2 = discreteMomentum p (elSolution p) := by
  simp only [elSolutionPhaseSpace]

-- ========================================================================
-- Axiom Audit
-- ========================================================================
-- All new theorems should be BISH: NO FanTheorem hypothesis.
-- Expected: [propext, Classical.choice, Quot.sound]
-- (Classical.choice from Mathlib's ℝ infrastructure, as always.)

#print axioms discreteMomentum
#print axioms legendreInverse
#print axioms legendre_invertible
#print axioms legendre_invertible'
#print axioms hamilton_eq1_satisfied
#print axioms hamilton_eq2_satisfied
#print axioms hamilton_eqs_satisfied
#print axioms hamilton_q_unique
#print axioms hamilton_p_unique
#print axioms hamilton_unique_solution
#print axioms legendre_consistency

end

end Papers.P28
