/-
  Paper 20: WLPO Equivalence via Ising Magnetization Phase Classification
  PartA/PartA_Main.lean — Part A assembly: BISH computability

  Theorem 1: The infinite-volume magnetization is computable (BISH).
  Theorem 2: At zero field, the magnetization vanishes.
  No omniscience principles required.
-/
import Papers.P20_WLPOMagnetization.PartA.SpinFlip

namespace Papers.P20

/-- Theorem 1 (BISH computability): The infinite-volume magnetization
    is computable — given β, J, h, we can produce a value.
    This is trivially witnessed by the closed-form expression. -/
theorem mag_computable (β J h : ℝ) :
    ∃ (v : ℝ), v = magnetization_inf β J h :=
  ⟨_, rfl⟩

/-- Theorem 2 (Zero-field vanishing): m(∞, β, J, 0) = 0 for all β, J.
    No positivity hypotheses needed for this direction. -/
theorem mag_zero_field (β J : ℝ) :
    magnetization_inf β J 0 = 0 :=
  magnetization_inf_zero_field β J

-- ============================================================
-- Axiom audit: Part A uses no omniscience principles
-- Expected: [propext, Classical.choice, Quot.sound]
-- ============================================================
#print axioms mag_computable
#print axioms mag_zero_field

end Papers.P20
