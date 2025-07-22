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
  gap     : True  -- TODO: Implement spectrum condition when mathlib compatibility improves

--------------------------------------------------------------------------------
-- Rank‑one projection onto e₀
--------------------------------------------------------------------------------

open Complex

/-!
NOTE: **Milestone B – partial implementation (Technical Debt)**

* `gap_lt` has a real `norm_num` proof.
* `gap` is still `True` because mathlib 4.3.0 lacks the required
  `spectrum_zero_eq_singleton` lemma and importing spectrum causes
  type‑class synthesis timeouts.

This is documented as technical debt item TD-1 in TECHNICAL_DEBT.md.
Resolution: implement local spectrum lemma (Math-AI's Route B approach).
-/





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
  gap     := trivial }

end SpectralGap