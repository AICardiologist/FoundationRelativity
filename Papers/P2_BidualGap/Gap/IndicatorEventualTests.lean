/-
Pin‑safe smoke tests for the spec ↔ eventual-zero bridge.
-/
import Papers.P2_BidualGap.Gap.IndicatorEventual

open Classical
open Papers.P2.Gap.BooleanSubLattice

section
  variable (A B : Set ℕ)

  -- A ≡ A (mod c₀ spec) ⇔ the difference is (trivially) eventually zero.
  example : indicatorEqModC0Spec A A ↔
      EventuallyZero (fun n => χ A n - χ A n) := by
    exact indicatorEqModC0_spec_iff_eventuallyZero (A := A) (B := A)

  -- Concrete sanity: {0} vs ∅
  example : indicatorEqModC0Spec ({0} : Set ℕ) (∅ : Set ℕ) := by
    -- symmDiff {0} ∅ = {0}, which is finite
    unfold indicatorEqModC0Spec finiteSymmDiff Papers.P2.Gap.BooleanSubLattice.symmDiff
    simp [Set.diff_empty, Set.union_empty]
end