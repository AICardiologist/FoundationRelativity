/-
  Paper 24: LLPO Equivalence via Kochen-Specker Contextuality
  PartB/Backward.lean — KSSignDecision implies LLPO (novel direction)

  Given α : ℕ → Bool with AtMostOne, construct the KS asymmetry.
  Apply the sign oracle:
    ksAsymmetry α ≤ 0  →  ∀ n, α(2n) = false     (left disjunct)
    0 ≤ ksAsymmetry α  →  ∀ n, α(2n+1) = false    (right disjunct)

  This is the novel/hard direction. No custom axioms needed.
-/
import Papers.P24_KochenSpecker.PartB.SignIff
import Papers.P24_KochenSpecker.Defs.LLPO

namespace Papers.P24

/-- Theorem (Backward / Novel direction):
    KSSignDecision implies LLPO.

    Given any binary sequence α with AtMostOne, we construct the
    KS asymmetry and apply the sign oracle.

    Note: KSSignDecision is stated inline to avoid importing
    the axiom llpo_real_of_llpo (which lives in Forward.lean). -/
theorem llpo_of_ks_sign
    (hks : ∀ (α : ℕ → Bool), AtMostOne α →
      ksAsymmetry α ≤ 0 ∨ 0 ≤ ksAsymmetry α) :
    LLPO := by
  intro α hamo
  rcases hks α hamo with hle | hge
  · -- Case: ksAsymmetry α ≤ 0 → all even entries false
    exact Or.inl (ksAsymmetry_nonpos_implies_even_false α hamo hle)
  · -- Case: 0 ≤ ksAsymmetry α → all odd entries false
    exact Or.inr (ksAsymmetry_nonneg_implies_odd_false α hamo hge)

-- Axiom audit: NO custom axioms (KSSignDecision is a hypothesis)
-- Expected: [propext, Classical.choice, Quot.sound]
#print axioms llpo_of_ks_sign

end Papers.P24
