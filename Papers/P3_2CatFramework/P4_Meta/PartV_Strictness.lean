/-
  Papers/P4_Meta/PartV_Strictness.lean
  
  Strictness results: predecessors cannot prove what successors can.
  These are carried as named axioms (classical lower bounds).
-/
import Papers.P3_2CatFramework.P4_Meta.PartV_Collision

namespace Papers.P4Meta.PartV

open Papers.P4Meta

/-- Extension preserves consistency (classical metatheorem) -/
axiom extend_preserves_consistency (T : Theory) (φ : Formula) (hcons : Consistent T) :
    Consistent (Extend T φ)

/-- G2 lower bound: T cannot prove its own consistency (Gödel's second incompleteness) -/
axiom G2_lower (T : Theory) [HBL T] [RE T] (hcons : Consistent T) :
    ¬T.Provable (Con T)

/-- G1 lower bound: T cannot prove its Gödel sentence (Gödel's first incompleteness) -/
axiom G1_lower (T : Theory) [HBL T] [RE T] (hcons : Consistent T) :
    ¬T.Provable (GodelSentence T)

/-- Strictness pair for reflection: successor proves Con(T), predecessor doesn't -/
theorem reflection_strictness (T : Theory) [HBL T] [RE T] (hcons : Consistent T)
    [CodesProofs T] [Sigma1Sound T] :
    (Extend T (RFN_Sigma1 T)).Provable (Con T) ∧ ¬T.Provable (Con T) := by
  constructor
  · exact reflection_implies_consistency T
  · exact G2_lower T hcons

/-- Strictness pair for consistency: successor proves G_T, predecessor doesn't -/
theorem consistency_strictness (T : Theory) [HBL T] [RE T] (hcons : Consistent T) :
    (Extend T (Con T)).Provable (GodelSentence T) ∧ ¬T.Provable (GodelSentence T) := by
  constructor
  · exact consistency_implies_godel T
  · exact G1_lower T hcons

/-- The collision is strict at each step -/
theorem collision_strictness (T : Theory) [HBL T] [RE T] (hcons : Consistent T)
    [CodesProofs T] [Sigma1Sound T] :
    let T1 := Extend T (RFN_Sigma1 T)
    let T2 := Extend T1 (Con T)
    (¬T.Provable (Con T)) ∧ 
    (T1.Provable (Con T) ∧ ¬T1.Provable (GodelSentence T)) ∧
    (T2.Provable (GodelSentence T)) := by
  constructor
  · exact G2_lower T hcons
  constructor
  · constructor
    · exact reflection_implies_consistency T
    · -- Extended theory remains consistent (classical metatheorem)
      have hcons' : Consistent (Extend T (RFN_Sigma1 T)) := extend_preserves_consistency T _ hcons
      have : HBL (Extend T (RFN_Sigma1 T)) := extend_preserves_HBL T _
      have : RE (Extend T (RFN_Sigma1 T)) := extend_preserves_RE T _
      exact G1_lower (Extend T (RFN_Sigma1 T)) hcons'
  · exact collision_chain T

end Papers.P4Meta.PartV