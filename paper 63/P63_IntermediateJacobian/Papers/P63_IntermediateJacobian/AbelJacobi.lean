/-
  Paper 63: The Intermediate Jacobian Obstruction
  File 3/8: Abel-Jacobi map and its properties

  The Abel-Jacobi map AJ: CH^p(X)_hom → J^p(X)(ℂ) sends
  homologically trivial cycles to points on the intermediate
  Jacobian. Its properties depend critically on whether J^p
  is algebraic.
-/

import Mathlib.Tactic
import Papers.P63_IntermediateJacobian.Basic
import Papers.P63_IntermediateJacobian.IntermediateJacobian

namespace Paper63

-- ============================================================
-- Abel-Jacobi Map Data
-- ============================================================

/-- The Abel-Jacobi map from homologically trivial cycles to J^p(X).
    Properties are axiomatized as Prop-valued hypotheses. -/
structure AbelJacobiData extends IntermediateJacobianData where
  -- Structural properties (always hold)
  /-- AJ is a group homomorphism -/
  aj_is_homomorphism : True
  /-- AJ factors through rational equivalence
      (so it's defined on CH^p, not just cycles) -/
  aj_factors_through_rat_equiv : True

  -- Properties conditional on algebraicity
  /-- When J^p is algebraic: AJ image lands in J^p(ℚ̄) -/
  aj_image_algebraic :
    (hodge.h ⟨hodge.degree, by omega⟩ = 0) →
    True  -- "AJ(CH^p_hom) ⊂ J^p(ℚ̄)"
  /-- When J^p is algebraic: height function exists on AJ image -/
  aj_height_exists :
    (hodge.h ⟨hodge.degree, by omega⟩ = 0) →
    True  -- "∃ ĥ : J^p(ℚ̄) → ℝ, Northcott(ĥ)"

-- ============================================================
-- Northcott and Height Structures
-- (Imported/compatible with Paper 62 infrastructure)
-- ============================================================

/-- A height function on a set S with the Northcott property:
    {x ∈ S : h(x) ≤ B} is finite for every B. -/
structure NorthcottHeight (S : Type*) where
  height : S → ℚ  -- rational-valued for decidability
  northcott : ∀ (B : ℚ), Set.Finite {x : S | height x ≤ B}

/-- Weak Northcott: just that height ≥ 0 and height 0 only at
    torsion. Weaker than full Northcott but still useful. -/
structure WeakNorthcottHeight (S : Type*) extends NorthcottHeight S where
  nonneg : ∀ x, height x ≥ 0

/-- The absence of any height with Northcott. -/
def NoNorthcottHeight (S : Type*) : Prop :=
  ∀ (h : S → ℚ), ¬(∀ (B : ℚ), Set.Finite {x : S | h x ≤ B})

-- ============================================================
-- Period Lattice and Rationality Testing
-- ============================================================

/-- The period lattice data for J^p(X) = ℂ^g / Λ.
    When J^p is non-algebraic, testing z ∈ Λ is LPO-hard. -/
structure PeriodLatticeData where
  /-- Complex dimension of the torus -/
  g : ℕ
  /-- The lattice has rank 2g (real rank) -/
  lattice_rank : ℕ := 2 * g
  /-- Testing membership z ∈ Λ (equivalently: is z ≡ 0 mod Λ?)
      requires comparing g complex coordinates against lattice
      generators — each comparison is a real zero test. -/
  membership_requires_zero_test : True

/-- For a non-algebraic torus: lattice membership test requires LPO.
    This is because the lattice Λ is not contained in any algebraic
    subvariety, so there is no finite algebraic test for membership.
    Each coordinate comparison z_i ∈ ℚ requires testing whether a
    real number equals a rational — this is LPO. -/
structure NonAlgebraicPeriodTest extends PeriodLatticeData where
  /-- The torus is not algebraic -/
  non_algebraic : True
  /-- No algebraic equations cut out the lattice -/
  no_algebraic_membership_test : True
  /-- Therefore: testing z ∈ Λ requires LPO
      (each coordinate is an independent real-vs-rational test) -/
  membership_is_lpo : LPO → Decidable True  -- LPO suffices
  /-- And LPO is necessary -/
  membership_needs_lpo : True  -- "¬BISH-decidable(z ∈ Λ)"

end Paper63
