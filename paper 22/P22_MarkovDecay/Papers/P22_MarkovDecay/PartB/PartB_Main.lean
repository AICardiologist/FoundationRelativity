/-
  Paper 22: Markov's Principle and the Constructive Cost of Eventual Decay
  PartB/PartB_Main.lean — Main equivalence: MP ↔ EventualDecay

  Central result: deciding whether a nucleus with nonzero decay rate
  eventually decays has exactly the logical strength of Markov's Principle.
-/
import Papers.P22_MarkovDecay.PartB.Forward
import Papers.P22_MarkovDecay.PartB.Backward

namespace Papers.P22

/-- Theorem 6 (Main Equivalence):
    Markov's Principle ↔ EventualDecay.

    The forward direction uses the interface axiom mp_real_of_mp.
    The backward direction requires no custom axioms. -/
theorem mp_iff_eventualDecay : MarkovPrinciple ↔ EventualDecay :=
  ⟨eventualDecay_of_mp, mp_of_eventualDecay⟩

-- Axiom audit
-- Expected: [propext, Classical.choice, Quot.sound, mp_real_of_mp]
#print axioms mp_iff_eventualDecay

end Papers.P22
