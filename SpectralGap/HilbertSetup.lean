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

namespace SpectralGap

/-- **Canonical Hilbert space** - the ℓ² space over complex numbers. -/
abbrev L2Space : Type := lp (fun _ : ℕ => ℂ) 2

/-- *Bounded* (continuous linear) operators placeholder.  Again, the real
    version will be `L2Space →L[ℂ] L2Space`; here a plain function keeps
    the file compiling. -/
abbrev BoundedOp : Type := L2Space → L2Space

/-- Marker: "`T` is compact".  Implementation postponed. -/
abbrev IsCompact (T : BoundedOp) : Prop := True

/-- Marker: "`T` is self‑adjoint".  Implementation postponed. -/
abbrev IsSelfAdjoint (T : BoundedOp) : Prop := True

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

end SpectralGap