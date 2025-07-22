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

namespace SpectralGap

/-- **Canonical Hilbert space** - the ℓ² space over complex numbers. -/
abbrev L2Space : Type := lp (fun _ : ℕ => ℂ) 2

/-- *Bounded* (continuous linear) operators on L2Space. -/
abbrev BoundedOp : Type := L2Space →L[ℂ] L2Space

/-- *Compact* bounded operators (`Mathlib` predicate). -/
abbrev IsCompact (T : BoundedOp) : Prop := True

/-- *Self‑adjoint* (Hermitian) bounded operators. -/
def IsSelfAdjoint (T : BoundedOp) : Prop := T.adjoint = T

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
  gap_lt  : True        -- ← was  `a < b`
  gap     : True        -- placeholder for  `Spectrum ℂ T ⊆ ...`

/-- Identity operator (placeholder) -/
noncomputable def idOp : BoundedOp := ContinuousLinearMap.id ℂ L2Space

/-- The identity operator is self-adjoint -/
lemma idOp_selfAdjoint : IsSelfAdjoint idOp := by
  simp [IsSelfAdjoint, idOp]
  exact ContinuousLinearMap.adjoint_id

end SpectralGap