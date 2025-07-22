/-
  Sprint S6 ▸ Milestone A
  Spectral-Gap (ρ = 3)  –  Hilbert‑space preliminaries

  This file sets up the ℓ² Hilbert space, the type of bounded operators,
  and a bundled record `SpectralGapOperator` that packages
  "compact + self‑adjoint + open spectral gap".  No mathematics is done
  here; the goal is to provide well‑named definitions that later proofs
  can import without pulling half of `Mathlib` everywhere.
-/

import Mathlib.Analysis.NormedSpace.lpSpace
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Analysis.NormedSpace.CompactOperator

open Complex
open scoped BigOperators ENNReal

namespace SpectralGap

/-- **Canonical Hilbert space** used throughout the construction. -/
abbrev ℓ² : Type _ := lp (fun _ : ℕ => ℂ) 2

instance : InnerProductSpace ℂ ℓ² := by
  infer_instance

instance : CompleteSpace ℓ² := by
  infer_instance

/-- Bounded (continuous linear) operators on `ℓ²`. -/
abbrev BoundedOp := ℓ² →L[ℂ] ℓ²

/-- *Compact* bounded operators (`Mathlib` predicate). -/
abbrev IsCompact (T : BoundedOp) : Prop := CompactOperator ℂ T

/-- *Self‑adjoint* (Hermitian) bounded operators. -/
def IsSelfAdjoint (T : BoundedOp) : Prop :=
  T.adjoint = T

/-- Bundles: compact ⨯ self‑adjoint operator having a *real* open
    interval `(a,b)` that is disjoint from its spectrum.
    We record `gap_lt : a < b` for convenience.
-/
structure SpectralGapOperator where
  T        : BoundedOp
  compact  : IsCompact T
  selfAdj  : IsSelfAdjoint T
  a b      : ℝ
  gap_lt   : a < b
  gap      : True  -- Placeholder for spectrum condition

end SpectralGap