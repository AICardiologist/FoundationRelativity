/-
  Paper 21: Bell Nonlocality and the Constructive Cost of Disjunction: LLPO
  PartB/Backward.lean — BellSignDecision implies LLPO (novel direction)

  Given α : ℕ → Bool with AtMostOne, construct the bell asymmetry.
  Apply the sign oracle:
    bellAsymmetry α ≤ 0  →  ∀ n, α(2n) = false     (left disjunct)
    0 ≤ bellAsymmetry α  →  ∀ n, α(2n+1) = false    (right disjunct)
-/
import Papers.P21_BellLLPO.PartB.SignIff
import Papers.P21_BellLLPO.Defs.LLPO

namespace Papers.P21

/-- Theorem 5 (Backward / Novel direction):
    BellSignDecision implies LLPO.

    Given any binary sequence α with AtMostOne, we construct the
    Bell asymmetry and apply the sign oracle.

    Note: BellSignDecision is stated inline to avoid importing
    the axiom llpo_real_of_llpo (which lives in Forward.lean). -/
theorem llpo_of_bell_sign
    (hbs : ∀ (α : ℕ → Bool), AtMostOne α →
      bellAsymmetry α ≤ 0 ∨ 0 ≤ bellAsymmetry α) :
    LLPO := by
  intro α hamo
  rcases hbs α hamo with hle | hge
  · -- Case: bellAsymmetry α ≤ 0 → all even entries false
    exact Or.inl (bellAsymmetry_nonpos_implies_even_false α hamo hle)
  · -- Case: 0 ≤ bellAsymmetry α → all odd entries false
    exact Or.inr (bellAsymmetry_nonneg_implies_odd_false α hamo hge)

-- Axiom audit: NO custom axioms (BellSignDecision is a hypothesis)
-- Expected: [propext, Classical.choice, Quot.sound]
#print axioms llpo_of_bell_sign

end Papers.P21
