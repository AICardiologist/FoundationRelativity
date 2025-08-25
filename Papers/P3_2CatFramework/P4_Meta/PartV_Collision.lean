/-
  Papers/P4_Meta/PartV_Collision.lean
  
  Core collision theorems: successor theories prove what predecessors cannot.
  These are the schematic versions that will be instantiated with actual theories.
-/
import Papers.P3_2CatFramework.P4_Meta.PartV_Interfaces
import Papers.P3_2CatFramework.P4_Meta.PartV_Reflection
import Papers.P3_2CatFramework.P4_Meta.Meta_Ladders

namespace Papers.P4Meta.PartV

open Papers.P4Meta

/-- Convenience wrapper: use the schematic RFNΣ¹ ⇒ Con inside collision proofs. -/
theorem Con_of_RFN_semantic (Text Tbase : Theory)
  (h : HasRFN_Sigma1 Text Tbase) : Papers.P4Meta.Con Tbase :=
  RFN_implies_Con Text Tbase h

-- (Optional) If older proofs assumed a bare `Con T`, you can now pass `Con_of_RFN Text T h`.
-- No other changes needed here; proofs can remain as-is.

/-- Reflection step: Adding RFN_Σ₁(T) allows proving Con(T) -/
theorem reflection_implies_consistency (T : Theory) [HBL T] [RE T] 
    [CodesProofs T] [Sigma1Sound T] :
    (Extend T (RFN_Sigma1 T)).Provable (Con T) := 
  reflection_implies_consistency_proved T

/-- Consistency step: Adding Con(T) allows proving the Gödel sentence G_T -/
axiom consistency_implies_godel (T : Theory) [HBL T] [RE T] :
    (Extend T (Con T)).Provable (GodelSentence T)

/-- The collision chain: two extension steps from T to prove G_T -/
theorem collision_chain (T : Theory) [HBL T] [RE T] 
    [CodesProofs T] [Sigma1Sound T] :
    (Extend (Extend T (RFN_Sigma1 T)) (Con T)).Provable (GodelSentence T) := by
  -- Let typeclass search supply the instances
  have _ : HBL (Extend T (RFN_Sigma1 T)) := inferInstance
  have _ : RE (Extend T (RFN_Sigma1 T)) := inferInstance
  exact consistency_implies_godel (Extend T (RFN_Sigma1 T))

/-- Height analysis: G_T has height ≤ 2 in the double extension -/
theorem godel_height_bound (T : Theory) [HBL T] [RE T] 
    [CodesProofs T] [Sigma1Sound T] :
    ∃ n, n ≤ 2 ∧ ProofHeight (Extend (Extend T (RFN_Sigma1 T)) (Con T)) (GodelSentence T) n := by
  refine ⟨0, ?_, ?_⟩
  · decide
  · apply ProofHeight.base
    exact collision_chain T

end Papers.P4Meta.PartV