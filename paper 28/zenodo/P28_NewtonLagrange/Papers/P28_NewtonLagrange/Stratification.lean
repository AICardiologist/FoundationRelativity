/-
  Paper 28: Newton vs. Lagrange — Constructive Stratification of Classical Mechanics
  Stratification.lean — Main theorem: constructive stratification of classical mechanics

  **Main Theorem (Stratification).**  For the discrete harmonic oscillator
  with N=2 time steps, compact configuration space [0,1], mass m > 0,
  spring constant k > 0, and stability condition k < 8m:

  1. (BISH) The Euler-Lagrange equation dS/dq = 0 has a unique solution
     q* = 4m(A+B)/(8m−k), computed constructively.  No Fan Theorem needed.

  2. (FT) The assertion that every continuous function on [0,1] attains
     its minimum — equivalently, that the action S attains its minimum —
     is equivalent to the Fan Theorem.

  Therefore the Newtonian (equation-of-motion) formulation and the
  Lagrangian (variational/optimization) formulation are constructively
  stratified: BISH versus FT.

  **Corollary.**  The variational interpretation of classical mechanics
  is logically dispensable — the equations are the physical content;
  the optimization is a framing whose existence claim costs FT.
-/
import Papers.P28_NewtonLagrange.BISHHalf
import Papers.P28_NewtonLagrange.FTHalf
import Papers.P28_NewtonLagrange.HamiltonBISH

namespace Papers.P28

-- ========================================================================
-- Main Stratification Theorem
-- ========================================================================

/-- **Stratification of Classical Mechanics.**

    The discrete harmonic oscillator (N=2) exhibits a clean constructive
    separation between its two formulations:

    • **Part 1 (BISH):** The Euler-Lagrange equation (8m−k)q = 4m(A+B) has
      a unique solution. The proof is purely algebraic — no choice principles,
      no Fan Theorem. This is the Newtonian (equation-of-motion) content.

    • **Part 2 (FT):** Universal minimizer existence on [0,1] is equivalent
      to the Fan Theorem. The harmonic action is continuous, so FT gives a
      minimizer; conversely, universal minimizer existence implies FT via
      EVT_min → EVT_max. This is the Lagrangian (variational) content.

    **Methodological note on the axiom audit.** All theorems in this bundle
    report `[propext, Classical.choice, Quot.sound]` because Mathlib's ℝ is
    constructed via classical Cauchy completion and `Classical.choice` pervades
    the ambient type. The constructive stratification is therefore established
    by the *mathematical content* of the proofs, not by `#print axioms`:
    the BISH half uses only explicit witness construction and algebraic
    manipulation (`field_simp`, `linarith`), while the FT half proceeds by
    reduction to `FanTheorem` carried as a hypothesis. The axiom audit
    distinguishes which theorems depend on FT *as a hypothesis*; it does not
    (and cannot, over Mathlib's ℝ) distinguish classical from constructive
    reasoning in the ambient type theory. See Paper 10 §Methodology for the
    full discussion of this standing limitation. -/
theorem stratification (p : HOParams) (hcfl : p.k < 8 * p.m) :
    -- Part 1: BISH solves the EL equation
    (∃! q : ℝ, (8 * p.m - p.k) * q = 4 * p.m * (p.A + p.B))
    ∧
    -- Part 2: Minimizer existence ↔ Fan Theorem
    ((∀ (f : ℝ → ℝ), ContinuousOn f (Set.Icc 0 1) →
       ∃ x ∈ Set.Icc (0 : ℝ) (1 : ℝ), ∀ y ∈ Set.Icc (0 : ℝ) (1 : ℝ), f x ≤ f y)
     ↔ FanTheorem) :=
  ⟨el_unique_solution_N2 p hcfl, minimizer_iff_ft⟩

/-- **Corollary.** The Fan Theorem is dispensable for solving the
    equations of motion, but indispensable for asserting the existence
    of an action-minimizing path.

    Concretely: the BISH half gives an explicit solution to the EL equation,
    while the FT half shows that asserting a minimizer exists requires FT. -/
theorem ft_dispensable_for_el (p : HOParams) (hcfl : p.k < 8 * p.m) :
    ∃! q : ℝ, (8 * p.m - p.k) * q = 4 * p.m * (p.A + p.B) :=
  el_unique_solution_N2 p hcfl

theorem ft_needed_for_minimizer :
    (∀ (f : ℝ → ℝ), ContinuousOn f (Set.Icc 0 1) →
      ∃ x ∈ Set.Icc (0 : ℝ) (1 : ℝ), ∀ y ∈ Set.Icc (0 : ℝ) (1 : ℝ), f x ≤ f y)
    → FanTheorem :=
  minimizer_iff_ft.mp

-- ========================================================================
-- Three-Way Stratification (Newton vs Lagrange vs Hamilton)
-- ========================================================================

/-- **Three-Way Stratification of Classical Mechanics.**

    The discrete harmonic oscillator (N=2) exhibits a clean constructive
    separation across all three textbook formulations:

    • **Part 1 (BISH):** The Euler-Lagrange equation has a unique solution.
    • **Part 2 (BISH):** Hamilton's equations have a unique solution.
    • **Part 3 (BISH):** The Legendre transform is an invertible bridge.
    • **Part 4 (FT):**  Minimizer existence ↔ Fan Theorem.

    All equation-solving is BISH. All optimization is FT.
    The bridge between formulations is BISH. -/
theorem stratification_triad (p : HOParams) (hcfl : p.k < 8 * p.m) :
    -- Part 1: BISH solves the EL equation (Lagrangian)
    (∃! q : ℝ, (8 * p.m - p.k) * q = 4 * p.m * (p.A + p.B))
    ∧
    -- Part 2: BISH solves Hamilton's equations
    ((∃! q : ℝ, satisfiesHamiltonEq2 p q)
     ∧ (∀ q : ℝ, ∃! mom : ℝ, satisfiesHamiltonEq1 p q mom))
    ∧
    -- Part 3: Legendre transform is invertible (BISH bridge)
    (∀ q : ℝ, legendreInverse p (discreteMomentum p q) = q)
    ∧
    -- Part 4: Minimizer existence ↔ Fan Theorem
    ((∀ (f : ℝ → ℝ), ContinuousOn f (Set.Icc 0 1) →
       ∃ x ∈ Set.Icc (0 : ℝ) (1 : ℝ), ∀ y ∈ Set.Icc (0 : ℝ) (1 : ℝ), f x ≤ f y)
     ↔ FanTheorem) :=
  ⟨el_unique_solution_N2 p hcfl,
   hamilton_unique_solution p hcfl,
   legendre_invertible p,
   minimizer_iff_ft⟩

-- ========================================================================
-- Axiom Audit
-- ========================================================================
-- All theorems report [propext, Classical.choice, Quot.sound].
-- Classical.choice is uniformly present because Mathlib's ℝ is constructed
-- via classical Cauchy completion — this is a standing limitation shared by
-- every paper in the series that works over Mathlib's reals.
--
-- The constructive stratification is verified by proof structure:
--   • BISH half: explicit witness (elSolution), algebraic verification
--     (field_simp, linarith). FanTheorem does NOT appear as hypothesis.
--   • FT half: FanTheorem enters as hypothesis; proof reduces minimizer
--     existence to EVT_min, which is equivalent to FanTheorem = EVT_max.
--
-- Zero custom axioms. Zero sorry. See Paper 10 §Methodology.

#print axioms el_unique_solution_N2
-- [propext, Classical.choice, Quot.sound] — BISH (no FT hypothesis)

#print axioms minimizer_iff_ft
-- [propext, Classical.choice, Quot.sound] — pure logic (EVT_max ↔ EVT_min)

#print axioms minimizer_of_ft
-- [propext, Classical.choice, Quot.sound] — FT enters as hypothesis

#print axioms stratification
-- [propext, Classical.choice, Quot.sound] — union of above

#print axioms ft_dispensable_for_el
#print axioms ft_needed_for_minimizer

-- Hamilton extension (all should be BISH — no FT hypothesis)
#print axioms legendre_invertible
#print axioms hamilton_unique_solution
#print axioms stratification_triad

end Papers.P28
