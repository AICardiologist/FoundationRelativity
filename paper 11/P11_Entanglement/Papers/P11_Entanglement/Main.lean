/-
Papers/P11_Entanglement/Main.lean
Paper 11: Constructive Cost of Quantum Entanglement — CRM over Mathlib.

Assembly of the two main results:
  Part A: Tsirelson bound — |⟨ψ, Cψ⟩| ≤ 2√2  (BISH)
  Part B: Bell state entropy — S(ρ_A) = log 2    (BISH)

Both are fully constructive: no omniscience or choice principles required.
This confirms the working hypothesis of Paper 10: the compositional structure
of quantum mechanics (tensor products, entanglement, Bell nonlocality) is
constructively accessible. Non-constructivity enters only through
infinite-dimensional idealization, not from relational structure.

Axiom profile: propext, Classical.choice, Quot.sound only.
No custom axioms. No sorry (when complete).
-/
import Papers.P11_Entanglement.TsirelsonBound
import Papers.P11_Entanglement.BellState

namespace Papers.P11

-- ========================================================================
-- Part A: Tsirelson bound — CHSH ≤ 2√2
-- ========================================================================

#check @tsirelson_bound

-- ========================================================================
-- Part B: Bell state entanglement entropy
-- ========================================================================

#check @bell_partialTrace
#check @bell_entropy
#check @bell_maximal_entanglement

-- ========================================================================
-- Axiom audit
-- ========================================================================

-- Part A: Tsirelson bound
#print axioms tsirelson_bound

-- Part B: Bell state
#print axioms bell_partialTrace
#print axioms bell_entropy
#print axioms bell_maximal_entanglement

-- Binary entropy
#print axioms binaryEntropy_half

end Papers.P11
