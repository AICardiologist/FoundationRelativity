/-
Pin‑safe smoke tests for the c0Spec bridge.
-/
import Papers.P2_BidualGap.Gap.C0Spec
open Classical
open Papers.P2.Gap.BooleanSubLattice

section
  variable (A B : Set ℕ)

  -- Trivial sanity: A ≡ A, and difference is identically zero.
  example :
      EventuallyZero (fun n => χ A n - χ A n)
      ↔ c0Spec (fun n => χ A n - χ A n) :=
    eventuallyZero_iff_c0Spec_indicator (A := A) (B := A)

  -- Concrete sanity: {0} vs ∅
  example :
      indicatorEqModC0Spec ({0} : Set ℕ) (∅ : Set ℕ)
      ↔ c0Spec (fun n => χ ({0} : Set ℕ) n - χ (∅ : Set ℕ) n) := by
    simpa using indicatorEqModC0_spec_iff_c0Spec
      (A := ({0} : Set ℕ)) (B := (∅ : Set ℕ))
end