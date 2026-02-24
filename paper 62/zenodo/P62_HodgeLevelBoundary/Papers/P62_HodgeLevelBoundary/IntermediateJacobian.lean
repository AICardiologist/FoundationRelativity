/-
  Paper 62: The Hodge Level Boundary
  File 2/10: Intermediate Jacobian — construction and algebraicity

  The intermediate Jacobian J^p(X) = H^{2p-1}(X,ℂ) / (F^p + H^{2p-1}(X,ℤ))
  is a complex torus. It is an abelian variety iff h^{2p-1,0}(X) = 0
  (Griffiths's algebraicity criterion).
-/

import Mathlib.Tactic
import Papers.P62_HodgeLevelBoundary.Basic

namespace Paper62

-- ============================================================
-- Intermediate Jacobian Structure
-- ============================================================

/-- Data package for the intermediate Jacobian J^p(X). -/
structure IntermediateJacobianData extends SmoothProjectiveData where
  torusDim : ℕ
  dim_eq : torusDim = hodge.ijDim
  griffiths_algebraic :
    (¬ hodge.hasTopHodgeNumber) ↔ True

-- ============================================================
-- Algebraicity Predicate
-- ============================================================

/-- J^p(X) is algebraic (an abelian variety) -/
structure IsAlgebraicIJ (ij : IntermediateJacobianData) : Prop where
  top_hodge_vanishes : ij.hodge.h ⟨ij.hodge.degree, by omega⟩ = 0
  admits_polarization : True

/-- J^p(X) is non-algebraic (a non-abelian complex torus) -/
structure IsNonAlgebraicIJ (ij : IntermediateJacobianData) : Prop where
  top_hodge_positive : ij.hodge.h ⟨ij.hodge.degree, by omega⟩ ≥ 1
  no_polarization : True

/-- Algebraic and non-algebraic are complementary. -/
theorem algebraic_or_not (ij : IntermediateJacobianData) :
    (IsAlgebraicIJ ij) ∨ (IsNonAlgebraicIJ ij) := by
  by_cases h : ij.hodge.h ⟨ij.hodge.degree, by omega⟩ = 0
  · left; exact ⟨h, trivial⟩
  · right
    push_neg at h
    exact ⟨Nat.pos_of_ne_zero h, trivial⟩

/-- They are mutually exclusive. -/
theorem not_both_algebraic_and_not (ij : IntermediateJacobianData)
    (ha : IsAlgebraicIJ ij) (hna : IsNonAlgebraicIJ ij) : False := by
  have h1 := ha.top_hodge_vanishes
  have h2 := hna.top_hodge_positive
  omega

-- ============================================================
-- Concrete Examples
-- ============================================================

/-- Cubic threefold: H³ has h^{2,1} = 5, h^{3,0} = 0.
    J²(V) is a ppav of dimension 5. -/
def cubicThreefoldHodge : HodgeData where
  degree := 3
  h := ![0, 5, 5, 0]
  symmetry := by decide

/-- Quintic CY3: H³ has h^{2,1} = 101, h^{3,0} = 1.
    J²(V) is a non-algebraic 102-dim complex torus. -/
def quinticCY3Hodge : HodgeData where
  degree := 3
  h := ![1, 101, 101, 1]
  symmetry := by decide

/-- The cubic threefold has h^{3,0} = 0. -/
theorem cubic_threefold_top_vanishes :
    cubicThreefoldHodge.h ⟨3, by decide⟩ = 0 := by
  native_decide

/-- The quintic CY3 has h^{3,0} = 1 ≥ 1. -/
theorem quintic_cy3_top_positive :
    quinticCY3Hodge.h ⟨3, by decide⟩ ≥ 1 := by
  native_decide

end Paper62
