/-
  Paper 20: WLPO Equivalence via Ising Magnetization Phase Classification
  PartB/Forward.lean — WLPO implies phase classification

  The forward direction uses the axiomatized bridge:
    WLPO → (∀ x : ℝ, x = 0 ∨ x ≠ 0)
  which is the real-valued form of WLPO (Bridges–Richman 1987).
-/
import Papers.P20_WLPOMagnetization.PartB.MagZeroIff
import Papers.P20_WLPOMagnetization.Defs.WLPO

namespace Papers.P20

/-- Interface axiom: WLPO for binary sequences implies WLPO for reals.
    This is a standard result from constructive mathematics
    (Bridges–Richman 1987, §3). -/
axiom wlpo_real_of_wlpo : WLPO → ∀ (x : ℝ), x = 0 ∨ x ≠ 0

/-- The phase classification of the 1D Ising magnetization.
    Deciding whether m(∞, β, J, h) = 0 or m(∞, β, J, h) ≠ 0. -/
def PhaseClassification : Prop :=
  ∀ (β J h : ℝ), 0 < β → 0 < J →
    magnetization_inf β J h = 0 ∨ magnetization_inf β J h ≠ 0

/-- Theorem 3 (Forward): WLPO implies phase classification.
    Given WLPO, we can decide for any real h whether h = 0 or h ≠ 0,
    then use m(∞) = 0 ↔ h = 0 to decide the magnetization. -/
theorem phase_classification_of_wlpo (hw : WLPO) : PhaseClassification := by
  intro β J h hβ hJ
  rcases wlpo_real_of_wlpo hw h with rfl | hne
  · left; exact (magnetization_inf_eq_zero_iff hβ hJ 0).mpr rfl
  · right; intro heq
    exact hne ((magnetization_inf_eq_zero_iff hβ hJ h).mp heq)

-- Axiom audit: uses wlpo_real_of_wlpo
#print axioms phase_classification_of_wlpo

end Papers.P20
