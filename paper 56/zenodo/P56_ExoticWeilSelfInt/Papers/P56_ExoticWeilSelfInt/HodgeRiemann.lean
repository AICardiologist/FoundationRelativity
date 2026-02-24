/-
  Paper 56 — Module 5: HodgeRiemann
  Exotic Weil Class Self-Intersection on CM Abelian Fourfolds

  Verifies the Hodge–Riemann bilinear relations for all three examples.
  For a primitive (2,2)-class on a fourfold, HR reduces to:
    deg(w · w) > 0.

  Sorry budget: 0. Pure sign checking.

  Paul C.-K. Lee, February 2026
-/
import Papers.P56_ExoticWeilSelfInt.SelfIntersection

/-! # Hodge–Riemann Verification

For a primitive class w ∈ H^{p,q}(X) on a compact Kähler manifold
of dimension n, the Hodge–Riemann bilinear relations require:

  (-1)^{k(k-1)/2} · i^{p-q} · deg(w · w̄) > 0

where k = p + q. For k = 4, p = q = 2:

  (-1)^6 · i^0 · deg(w · w) = deg(w · w) > 0

So HR for primitive (2,2)-classes on fourfolds reduces to positivity.
-/

-- ============================================================
-- HR sign computation
-- ============================================================

/-- The HR sign factor for a primitive (2,2)-class on a 4-fold.
  (-1)^{k(k-1)/2} · i^{p-q} where k=4, p=2, q=2.
  = (-1)^6 · i^0 = 1 · 1 = 1. -/
theorem hr_sign_factor : (-1 : ℤ) ^ 6 * 1 = 1 := by norm_num

/-- For (2,2)-classes on fourfolds, HR reduces to deg > 0. -/
def hr_satisfied_fourfold (deg : ℤ) : Prop := deg > 0

-- ============================================================
-- HR verification for all three examples
-- ============================================================

/-- **HR for Example 1:** deg(w₀ · w₀) = 7 > 0. ✓ -/
theorem hr_example1 :
    hr_satisfied_fourfold (deg_self_intersection ex1_generator) := by
  unfold hr_satisfied_fourfold
  rw [self_intersection_ex1]
  norm_num

/-- **HR for Example 2:** deg(w₀ · w₀) = 9 > 0. ✓ -/
theorem hr_example2 :
    hr_satisfied_fourfold (deg_self_intersection ex2_generator) := by
  unfold hr_satisfied_fourfold
  rw [self_intersection_ex2]
  norm_num

/-- **HR for Example 3:** deg(w₀ · w₀) = 13 > 0. ✓ -/
theorem hr_example3 :
    hr_satisfied_fourfold (deg_self_intersection ex3_generator) := by
  unfold hr_satisfied_fourfold
  rw [self_intersection_ex3]
  norm_num

/-- All three examples satisfy HR. -/
theorem hr_all :
    hr_satisfied_fourfold (deg_self_intersection ex1_generator) ∧
    hr_satisfied_fourfold (deg_self_intersection ex2_generator) ∧
    hr_satisfied_fourfold (deg_self_intersection ex3_generator) :=
  ⟨hr_example1, hr_example2, hr_example3⟩
