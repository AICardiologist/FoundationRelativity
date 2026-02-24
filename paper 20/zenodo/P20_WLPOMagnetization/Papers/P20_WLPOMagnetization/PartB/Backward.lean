/-
  Paper 20: WLPO Equivalence via Ising Magnetization Phase Classification
  PartB/Backward.lean — Phase classification implies WLPO (novel direction)

  Given α : ℕ → Bool, construct the encoded field h_α.
  Apply phase classification at β = 1, J = 1:
    m(∞, 1, 1, h_α) = 0  →  h_α = 0  →  ∀ n, α(n) = false
    m(∞, 1, 1, h_α) ≠ 0  →  h_α ≠ 0  →  ¬(∀ n, α(n) = false)
-/
import Papers.P20_WLPOMagnetization.PartB.MagZeroIff
import Papers.P20_WLPOMagnetization.Defs.EncodedField
import Papers.P20_WLPOMagnetization.Defs.WLPO

namespace Papers.P20

/-- Theorem 4 (Backward / Novel direction):
    Phase classification implies WLPO.

    Given any binary sequence α, we encode it as an external field h_α
    and apply the phase classification oracle at β = J = 1.

    Note: PhaseClassification is stated inline to avoid importing
    the axiom wlpo_real_of_wlpo (which lives in Forward.lean). -/
theorem wlpo_of_phase_classification
    (hpc : ∀ (β J h : ℝ), 0 < β → 0 < J →
      magnetization_inf β J h = 0 ∨ magnetization_inf β J h ≠ 0) :
    WLPO := by
  intro α
  -- Construct the encoded field
  set h_α := encodedField α with _hdef
  -- Apply phase classification at β = 1, J = 1
  rcases hpc 1 1 h_α one_pos one_pos with heq | hne
  · -- Case: m(∞, 1, 1, h_α) = 0 → h_α = 0 → ∀ n, α(n) = false
    left
    exact (encodedField_eq_zero_iff α).mp
      ((magnetization_inf_eq_zero_iff one_pos one_pos h_α).mp heq)
  · -- Case: m(∞, 1, 1, h_α) ≠ 0 → h_α ≠ 0 → ¬(∀ n, α(n) = false)
    right
    intro hall
    exact hne ((magnetization_inf_eq_zero_iff one_pos one_pos h_α).mpr
      ((encodedField_eq_zero_iff α).mpr hall))

-- Axiom audit: NO custom axioms (phase classification is a hypothesis)
-- Expected: [propext, Classical.choice, Quot.sound]
#print axioms wlpo_of_phase_classification

end Papers.P20
