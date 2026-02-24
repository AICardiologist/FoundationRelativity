/-
  Paper 43: What the Ceiling Means
  BISHContent/PoincareMeasure.lean — Theorem 3: Poincaré recurrence (BISH content)

  For a measure-preserving map φ on a finite measure space (X, μ),
  the set B = {x ∈ A : ∀k ≥ 1, φᵏ(x) ∉ A} has μ(B) = 0.

  Proof content is BISH: pairwise disjoint preimages with equal
  measure contradict finite total measure.

  Wraps Mathlib's Conservative.measure_mem_forall_ge_image_notMem_eq_zero.
-/
import Mathlib.Dynamics.Ergodic.Conservative

namespace Papers.P43

open MeasureTheory Set Function

-- ========================================================================
-- Definition: never-returning set
-- ========================================================================

/-- The set of points in A that never return under any positive iterate.
    B = {x ∈ A : ∀k ≥ 1, φᵏ(x) ∉ A}. -/
def neverReturn {α : Type*} (f : α → α) (A : Set α) : Set α :=
  {x ∈ A | ∀ k, 0 < k → f^[k] x ∉ A}

-- ========================================================================
-- Theorem 3: Poincaré non-return set has measure zero
-- ========================================================================

/-- Theorem 3 (Poincaré recurrence, BISH content).
    For a measure-preserving map on a finite measure space,
    the set of points in A that never return to A has measure zero.

    Proof: The preimages φ⁻ⁿ(B) are pairwise disjoint and equimeasured
    (measure preservation). If μ(B) > 0, their union has infinite measure,
    contradicting μ(X) < ∞. So μ(B) = 0.

    Wraps Mathlib: MeasurePreserving.conservative +
    Conservative.measure_mem_forall_ge_image_notMem_eq_zero. -/
theorem poincare_nonreturn_measure_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ]
    {f : α → α} (hf : MeasurePreserving f μ μ)
    {A : Set α} (hA : NullMeasurableSet A μ) :
    μ (neverReturn f A) = 0 := by
  have hcons := hf.conservative
  -- Mathlib gives us: for any n, μ {x ∈ A | ∀ m ≥ n, f^[m] x ∉ A} = 0
  -- We need n = 1 and to match our neverReturn definition
  have key := hcons.measure_mem_forall_ge_image_notMem_eq_zero hA 1
  -- Our neverReturn definition matches Mathlib's set at n=1
  convert key using 1

end Papers.P43
