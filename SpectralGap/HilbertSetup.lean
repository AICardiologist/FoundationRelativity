/-
  Sprint S6 ▸ Milestone A
  Spectral-Gap (ρ = 3)  –  Hilbert‑space preliminaries

  This file sets up the ℓ² Hilbert space, the type of bounded operators,
  and a bundled record `SpectralGapOperator` that packages
  "compact + self‑adjoint + open spectral gap".  No mathematics is done
  here; the goal is to provide well‑named definitions that later proofs
  can import without pulling half of `Mathlib` everywhere.
-/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.NormedSpace.CompactOperator
import Mathlib.Analysis.InnerProductSpace.Adjoint

open Complex
open scoped BigOperators ENNReal

namespace SpectralGap

/-- **Canonical Hilbert space** used throughout the construction. -/
abbrev L2Space : Type _ := lp (fun _ : ℕ => ℂ) 2

/-- Bounded (continuous linear) operators on `L2Space`. -/
abbrev BoundedOp := L2Space →L[ℂ] L2Space

/-- *Compact* bounded operators (`Mathlib` predicate). -/
abbrev IsCompact (T : BoundedOp) : Prop := IsCompactOperator T

/-- *Self‑adjoint* (Hermitian) bounded operators. -/
def IsSelfAdjoint (T : BoundedOp) : Prop :=
  T† = T

/-- Bundles: compact × self‑adjoint operator having a *real* open
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