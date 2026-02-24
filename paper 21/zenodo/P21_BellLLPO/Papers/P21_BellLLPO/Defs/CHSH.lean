/-
  Paper 21: Bell Nonlocality and the Constructive Cost of Disjunction: LLPO
  Defs/CHSH.lean — CHSH setup and definitions

  The CHSH (Clauser–Horne–Shimony–Holt) inequality setup:
  four dichotomic observables with outcomes ±1, the CHSH correlator,
  and the quantum violation value.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Papers.P21

-- ========================================================================
-- LHV (Local Hidden Variable) Assignment
-- ========================================================================

/-- A local hidden variable assignment: four dichotomic (±1) values.
    Using ℝ throughout to avoid Int/Real cast issues. -/
structure LHVAssignment where
  a₁ : ℝ  -- Alice's outcome for setting 1
  a₂ : ℝ  -- Alice's outcome for setting 2
  b₁ : ℝ  -- Bob's outcome for setting 1
  b₂ : ℝ  -- Bob's outcome for setting 2
  ha₁ : a₁ = 1 ∨ a₁ = -1
  ha₂ : a₂ = 1 ∨ a₂ = -1
  hb₁ : b₁ = 1 ∨ b₁ = -1
  hb₂ : b₂ = 1 ∨ b₂ = -1

-- ========================================================================
-- CHSH Expression
-- ========================================================================

/-- The CHSH correlator expression for a deterministic assignment.
    S = a₁b₁ + a₁b₂ + a₂b₁ - a₂b₂ -/
def chshExpr (m : LHVAssignment) : ℝ :=
  m.a₁ * m.b₁ + m.a₁ * m.b₂ + m.a₂ * m.b₁ - m.a₂ * m.b₂

-- ========================================================================
-- Quantum CHSH Value
-- ========================================================================

/-- The quantum CHSH value: S_Q = 2√2 (Tsirelson bound).
    Achieved by the singlet state with optimal measurement angles. -/
noncomputable def S_quantum : ℝ := 2 * Real.sqrt 2

end Papers.P21
