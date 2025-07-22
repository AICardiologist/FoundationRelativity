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
import Mathlib.Analysis.InnerProductSpace.PiL2

open Complex
open scoped BigOperators

namespace SpectralGap

/-- **Canonical Hilbert space** - the ℓ² space over complex numbers. -/
abbrev L2Space : Type := lp (fun _ : ℕ => ℂ) 2

/-- *Bounded* (continuous linear) operators on L2Space. -/
abbrev BoundedOp : Type := L2Space →L[ℂ] L2Space

/-- *Compact* bounded operators (`Mathlib` predicate). -/
abbrev IsCompact (T : BoundedOp) : Prop := IsCompactOperator T

/-- *Self‑adjoint* (Hermitian) bounded operators. -/
def IsSelfAdjoint (T : BoundedOp) : Prop :=
  ContinuousLinearMap.adjoint T = T

/-- Rank-one projection onto the first basis vector e₀ -/
noncomputable def proj₁ : BoundedOp :=
  ContinuousLinearMap.mk {
    toFun := fun f ↦ fun n ↦ if n = 0 then f 0 else 0,
    map_add' := by
      intro f g
      funext n
      by_cases h : n = 0 <;> simp [h],
    map_smul' := by
      intro c f  
      funext n
      by_cases h : n = 0 <;> simp [h]
  } (by
    -- The projection is bounded with norm ≤ 1
    use 1
    intro f
    simp [proj₁]
    sorry -- Proof that ||proj₁ f|| ≤ ||f|| for now
  )

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

/-- First concrete SpectralGapOperator using rank-one projection -/
noncomputable def projGapOp : SpectralGapOperator := {
  T := proj₁,
  compact := by
    -- Finite-rank operators are compact
    sorry, -- Will need to prove proj₁ is finite rank
  selfAdj := by
    -- Projection operators are self-adjoint  
    sorry, -- Will need to prove proj₁.adjoint = proj₁
  a := 0,
  b := 1, 
  gap_lt := by norm_num,
  gap := by
    -- Spectrum of projection is {0,1}, so gap holds
    sorry -- Will need spectrum analysis
}

end SpectralGap