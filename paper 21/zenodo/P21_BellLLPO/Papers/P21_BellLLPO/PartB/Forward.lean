/-
  Paper 21: Bell Nonlocality and the Constructive Cost of Disjunction: LLPO
  PartB/Forward.lean — LLPO implies BellSignDecision

  The forward direction uses the axiomatized bridge:
    LLPO → (∀ x : ℝ, x ≤ 0 ∨ 0 ≤ x)
  which is the real-valued form of LLPO (Ishihara 2006).
-/
import Papers.P21_BellLLPO.Defs.EncodedAsymmetry

namespace Papers.P21

/-- Interface axiom: LLPO for binary sequences implies LLPO for reals.
    This is a standard result from constructive mathematics:
    LLPO implies that for every real x, either x ≤ 0 or 0 ≤ x.
    (Ishihara 2006, Bridges–Richman 1987, §4.3). -/
axiom llpo_real_of_llpo : LLPO → ∀ (x : ℝ), x ≤ 0 ∨ 0 ≤ x

/-- Theorem 4 (Forward): LLPO implies BellSignDecision.
    Given LLPO, we can decide the sign of any real number,
    in particular bellAsymmetry α. -/
theorem bell_sign_of_llpo (hllpo : LLPO) : BellSignDecision := by
  intro α _hamo
  exact llpo_real_of_llpo hllpo (bellAsymmetry α)

-- Axiom audit: uses llpo_real_of_llpo
-- Expected: [propext, Classical.choice, Quot.sound, llpo_real_of_llpo]
#print axioms bell_sign_of_llpo

end Papers.P21
