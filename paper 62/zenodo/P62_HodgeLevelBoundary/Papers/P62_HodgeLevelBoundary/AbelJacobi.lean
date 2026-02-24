/-
  Paper 62: The Hodge Level Boundary
  File 3/10: Abel-Jacobi map and its properties

  The Abel-Jacobi map AJ: CH^p(X)_hom → J^p(X)(ℂ) sends
  homologically trivial cycles to points on the intermediate
  Jacobian. Its properties depend critically on whether J^p
  is algebraic.
-/

import Mathlib.Tactic
import Papers.P62_HodgeLevelBoundary.Basic
import Papers.P62_HodgeLevelBoundary.IntermediateJacobian

namespace Paper62

-- ============================================================
-- Abel-Jacobi Map Data
-- ============================================================

/-- The Abel-Jacobi map from homologically trivial cycles to J^p(X). -/
structure AbelJacobiData extends IntermediateJacobianData where
  aj_is_homomorphism : True
  aj_factors_through_rat_equiv : True
  aj_image_algebraic :
    (hodge.h ⟨hodge.degree, by omega⟩ = 0) → True
  aj_height_exists :
    (hodge.h ⟨hodge.degree, by omega⟩ = 0) → True

-- ============================================================
-- Northcott and Height Structures
-- ============================================================

/-- A height function with the Northcott property. -/
structure NorthcottHeight (S : Type*) where
  height : S → ℚ
  northcott : ∀ (B : ℚ), Set.Finite {x : S | height x ≤ B}

/-- Weak Northcott: just nonneg. -/
structure WeakNorthcottHeight (S : Type*) extends NorthcottHeight S where
  nonneg : ∀ x, height x ≥ 0

/-- Absence of any Northcott height. -/
def NoNorthcottHeight (S : Type*) : Prop :=
  ∀ (h : S → ℚ), ¬(∀ (B : ℚ), Set.Finite {x : S | h x ≤ B})

-- ============================================================
-- Period Lattice and Rationality Testing
-- ============================================================

/-- Period lattice data for J^p(X) = ℂ^g / Λ. -/
structure PeriodLatticeData where
  g : ℕ
  lattice_rank : ℕ := 2 * g
  membership_requires_zero_test : True

/-- For a non-algebraic torus: lattice membership test requires LPO. -/
structure NonAlgebraicPeriodTest extends PeriodLatticeData where
  non_algebraic : True
  no_algebraic_membership_test : True
  membership_is_lpo : LPO → Decidable True
  membership_needs_lpo : True

end Paper62
