/-
  Paper 24: LLPO Equivalence via Kochen-Specker Contextuality
  PartB/Forward.lean — LLPO implies KSSignDecision

  The forward direction uses the axiomatized bridge:
    LLPO → (∀ x : ℝ, x ≤ 0 ∨ 0 ≤ x)
  which is the real-valued form of LLPO (Ishihara 2006).
-/
import Papers.P24_KochenSpecker.Defs.EncodedAsymmetry

namespace Papers.P24

/-- Interface axiom: LLPO for binary sequences implies LLPO for reals.
    This is a standard result from constructive mathematics:
    LLPO implies that for every real x, either x ≤ 0 or 0 ≤ x.
    (Ishihara 2006, Bridges–Richman 1987, §4.3). -/
axiom llpo_real_of_llpo : LLPO → ∀ (x : ℝ), x ≤ 0 ∨ 0 ≤ x

/-- Theorem (Forward): LLPO implies KSSignDecision.
    Given LLPO, we can decide the sign of any real number,
    in particular ksAsymmetry α. -/
theorem ks_sign_of_llpo (hllpo : LLPO) : KSSignDecision := by
  intro α _hamo
  exact llpo_real_of_llpo hllpo (ksAsymmetry α)

-- Axiom audit: uses llpo_real_of_llpo
-- Expected: [propext, Classical.choice, Quot.sound, llpo_real_of_llpo]
#print axioms ks_sign_of_llpo

end Papers.P24
