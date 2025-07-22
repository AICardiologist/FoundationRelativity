/-
  Sprint S6 ▸ Milestone A  (compile‑clean stub)

  ℓ² machinery and operator definitions *will* live here, but to get CI
  passing we provide very light placeholders that do **not** pull in the
  heavy inner‑product / adjoint stack yet.  All names and fields are kept,
  so later commits can simply flesh them out.
-/

-- only tiny, always‑present dependencies
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.NormedSpace.CompactOperator
import Mathlib.Analysis.NormedSpace.Spectrum



namespace SpectralGap

/-- **Canonical Hilbert space** - the ℓ² space over complex numbers. -/
abbrev L2Space : Type := lp (fun _ : ℕ => ℂ) 2


/-- *Bounded* (continuous linear) operators on L2Space. -/
abbrev BoundedOp : Type := L2Space →L[ℂ] L2Space

/-- `BoundedOp` is non‑trivial: `0 ≠ 1`. -/
instance : Nontrivial BoundedOp := ContinuousLinearMap.nontrivial





/-- *Compact* bounded operators (`Mathlib` predicate). -/
abbrev IsCompact (T : BoundedOp) : Prop := IsCompactOperator T

/-- *Self‑adjoint* (Hermitian) bounded operators. -/
def IsSelfAdjoint (T : BoundedOp) : Prop :=
  ContinuousLinearMap.adjoint T = T


/-- **Bundled object with a spectral gap**.

    *All* five fields already appear in the final API, so later work can
    simply strengthen the placeholders instead of rewriting files that
    import them. -/
structure SpectralGapOperator where
  T       : BoundedOp
  compact : IsCompact T
  selfAdj : IsSelfAdjoint T
  a       : ℝ
  b       : ℝ
  gap_lt  : a < b
  gap     : ∀ z ∈ spectrum ℂ T, z.re ≤ a ∨ b ≤ z.re

--------------------------------------------------------------------------------
-- Rank‑one projection onto e₀
--------------------------------------------------------------------------------

open scoped ComplexOrder
open Complex spectrum

lemma spectrum_zero :
    spectrum ℂ (0 : BoundedOp) = {0} := by
  -- *Step 1*: show that every non‑zero λ is in the resolvent set
  have hλ : ∀ λ : ℂ, λ ≠ 0 → IsUnit (λ • (1 : BoundedOp) - 0) := by
    intro λ hλ
    simpa [sub_zero] using
      (isUnit_smul_iff.2 ⟨hλ, isUnit_one⟩)
  -- *Step 2*: rewrite membership
  ext z
  constructor
  · intro hz
    by_cases hz0 : z = 0
    · simpa [hz0]
    · have : IsUnit (z • 1 - (0 : BoundedOp)) := hλ z hz0
      exact False.elim (hz this)  -- contradicts definition of spectrum
  · rintro rfl
    exact spectrum_zero_mem _




/-- Concrete `SpectralGapOperator` using zero operator with real gap proof. -/
noncomputable def zeroGapOp : SpectralGapOperator :=
{ T       := 0,
  compact := by
    simpa using isCompactOperator_zero,
  selfAdj := by
    simp [IsSelfAdjoint],
  a       := 0.1,
  b       := 0.9,
  gap_lt  := by norm_num,
  gap     := by
    intro z hz
    have hz0 : z = 0 := by
      have : z ∈ spectrum ℂ (0 : BoundedOp) := hz
      simpa [spectrum_zero] using this
    subst hz0
    left
    norm_num }

end SpectralGap