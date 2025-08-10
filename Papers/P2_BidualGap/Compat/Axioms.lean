/-
Papers/P2_BidualGap/Compat/Axioms.lean

Classical compat axioms that are NOT used in the core constructive equivalence.
Isolated here so they can be swapped out with real proofs later without touching downstream code.

⚠️  IMPORTANT: Any use of axioms from this file in Papers/P2_BidualGap/Constructive/* 
    will fail CI via Scripts/constructive_guard.sh. Keep the core constructive
    pipeline axiom-clean!
-/
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Group.Completeness

namespace Papers.P2.Compat.Axioms

/-- A *weak* non-reflexive witness over `𝕂` — classical notion. -/
def NonReflexiveWitness (𝕂 : Type*) [NontriviallyNormedField 𝕂] : Prop :=
  ∃ (X : Type*) (_ : NormedAddCommGroup X) (_ : NormedSpace 𝕂 X) (_ : CompleteSpace X),
    ¬ Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕂 X)

/-- (Classical stub) Concrete weak witness using standard non-reflexive spaces.
    
    In classical Banach space theory, spaces like c₀ (vanishing sequences)
    and ℓ¹ (summable sequences) are complete but not reflexive.
    This is standard classical theory, isolated as an axiom to avoid importing
    heavy Banach space machinery into the core constructive equivalence. -/
axiom c0_or_l1_witness_weak : NonReflexiveWitness ℝ

end Papers.P2.Compat.Axioms