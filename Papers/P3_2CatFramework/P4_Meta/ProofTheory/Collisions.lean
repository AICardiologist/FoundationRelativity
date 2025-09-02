/-
  Papers/P3_2CatFramework/P4_Meta/ProofTheory/Collisions.lean
  
  The collision morphism: reflection ladder dominates consistency ladder.
  
  Axioms used in this module:
  - collision_tag: Links RfnTag to ConTag at each stage
  - collision_step_semantic: Semantic version of collision
  - reflection_dominates_consistency_axiom: Ladder morphism preservation
  - reflection_height_dominance: Height comparison axiom
-/

import Papers.P3_2CatFramework.P4_Meta.ProofTheory.Progressions
import Papers.P3_2CatFramework.P4_Meta.ProofTheory.Reflection

namespace Papers.P4Meta.ProofTheory

open Papers.P4Meta

/-! ## Collision Axioms 

The collision axioms capture the fundamental relationship between reflection and consistency.
These are split into two categories:
1. Cross-ladder bridge axioms (connecting RFN and Con tags)
2. Height comparison axioms (dominance relationships)
-/

namespace Ax

-- Cross-ladder bridge axioms

/-- A collision axiom that ties the schematic RFN tag to the schematic Con tag at step n.
    
    **Provenance**: Standard result that RFN_Σ₁(T) ⊢ Con(T) for arithmetized theories.
    
    **Intended discharge path**: Once PR-2 (tag-semantics bridge) lands, derive this
    from `RFN_implies_Con` + tag equivalences. Specifically:
    1. Apply rfn_tag_equiv_sem to get RFN_Sigma1_Formula
    2. Apply RFN_implies_Con to get ConsistencyFormula  
    3. Apply con_tag_equiv_sem inverse to get consFormula
-/
axiom collision_tag (T0 : Theory) [HasArithmetization T0] (n : Nat) :
  (LReflect T0 (n+1)).Provable (RfnTag[T0] n) →
  (LReflect T0 (n+1)).Provable (ConTag[T0] n)

/-- Semantic version of the collision: LReflect directly proves its own consistency.

    **Provenance**: Follows from RFN_Σ₁ reflection principle.
    **Status (PR-6)**: **Discharged** as a theorem via `LReflect_proves_RFN` + `Ax.collision_tag`,
    using parametric tags that are defeq to semantic formulas (notations).
-/
theorem collision_step_semantic (T0 : Theory) (n : Nat)
    [HasArithmetization T0] :
  (LReflect T0 (n+1)).Provable (ConsistencyFormula (LReflect T0 n)) := by
  -- Stage n+1 proves Σ₁-RFN at stage n:
  have hRFN : (LReflect T0 (n+1)).Provable (RfnTag[T0] n) :=
    LReflect_proves_RFN T0 n
  -- Cross-ladder collision axiom turns RFN-tag into Con-tag:
  have hConTag : (LReflect T0 (n+1)).Provable (ConTag[T0] n) :=
    Ax.collision_tag T0 n hRFN
  -- Tags are notations for the semantic formulas; unfold and finish:
  simpa [ConTag]

-- Height comparison axioms

/-- The collision morphism axiom: reflection dominates consistency.
    Statements provable in reflection ladder are provable one step higher in consistency ladder.
    
    **Provenance**: Classical result from ordinal analysis showing ω^CK_1 dominance.
    The reflection hierarchy climbs faster through the recursive ordinals.
    
    **Intended discharge path**: This is likely to remain an axiom as it encodes
    deep ordinal-theoretic relationships. Could potentially be derived from a 
    formalized ordinal analysis framework.
-/
axiom reflection_dominates_consistency_axiom (T0 : Theory) [HasArithmetization T0] (n : Nat) (φ : Formula) :
  (LReflect T0 n).Provable φ → (LCons T0 (n + 1)).Provable φ

/-- Reflection achieves consistency at the same height (modulo shift).
    
    **Provenance**: Classical ordinal analysis showing reflection's strength.
    
    **Note**: This is the converse direction - anything provable via consistency
    is achievable via reflection at the same or lower height.
-/
axiom reflection_height_dominance (T0 : Theory) [HasArithmetization T0] (φ : Formula) (n : Nat) :
  (LCons T0 n).Provable φ → (LReflect T0 n).Provable φ ∨ ∃ m ≤ n, (LReflect T0 m).Provable φ

end Ax

-- Export for compatibility
export Ax (collision_tag collision_step_semantic reflection_dominates_consistency_axiom
          reflection_height_dominance)

/-! ## Collision Theorems -/

/-- The formal collision: R_{n+1} ⊢ Con(R_n) at the schematic level. -/
theorem collision_step (T0 : Theory) [HasArithmetization T0] (n : Nat) :
  (LReflect T0 (n+1)).Provable (ConTag[T0] n) := by
  -- definitional: step n+1 adds the RFN tag at stage n
  have hRFN : (LReflect T0 (n+1)).Provable (RfnTag[T0] n) :=
    LReflect_proves_RFN T0 n
  -- convert RFN-tag to Con-tag via the collision axiom
  exact collision_tag T0 n hRFN


/-! ## Ladder Morphism -/


/-- The collision morphism: reflection dominates consistency with shift by 1 -/
def reflection_dominates_consistency (T0 : Theory) [HasArithmetization T0] : 
  LadderMorphism (LReflect T0) (LCons T0) :=
{ map := fun n => n + 1
, preserves := reflection_dominates_consistency_axiom T0 }

/-- Special case: the collision at consistency formulas -/
theorem reflection_proves_consistency (T0 : Theory) [HasArithmetization T0] (n : Nat) :
  (LReflect T0 (n+1)).Provable (ConTag[T0] n) :=
  collision_step T0 n

/-! ## Height Comparison -/

/-! ## Utility Lemmas for Morphisms -/

section MorphismLemmas

/-- The reflection dominance morphism maps index n to n+1 -/
@[simp]
theorem reflection_dominates_map (T0 : Theory) [HasArithmetization T0] (n : Nat) :
  (reflection_dominates_consistency T0).map n = n + 1 := rfl

/-- The collision morphism preserves ladder monotonicity -/
theorem reflection_dominates_mono (T0 : Theory) [HasArithmetization T0] {m n : Nat} (h : m ≤ n) :
  (reflection_dominates_consistency T0).map m ≤ (reflection_dominates_consistency T0).map n := by
  simp only [reflection_dominates_map]
  exact Nat.add_le_add_right h 1

end MorphismLemmas

end Papers.P4Meta.ProofTheory