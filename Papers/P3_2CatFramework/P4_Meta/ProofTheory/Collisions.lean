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

/-! ## Collision Axioms -/

namespace Ax

/-- A collision axiom that ties the schematic RFN tag to the schematic Con tag at step n.
    Provenance: Reflection implies consistency at each stage; internalization deferred. -/
axiom collision_tag (T0 : Theory) (n : Nat) :
  (LReflect T0 (n+1)).Provable (reflFormula n) →
  (LReflect T0 (n+1)).Provable (consFormula n)

/-- Semantic version of the collision.
    Note: This requires a cross-ladder refinement axiom. -/
axiom collision_step_semantic (T0 : Theory) (n : Nat)
    [HasArithmetization T0] :
  (LReflect T0 (n+1)).Provable (ConsistencyFormula (LReflect T0 n))

/-- The collision morphism axiom: reflection dominates consistency.
    Provenance: Classical result from ordinal analysis; deferred for 3B. -/
axiom reflection_dominates_consistency_axiom (T0 : Theory) (n : Nat) (φ : Formula) :
  (LReflect T0 n).Provable φ → (LCons T0 (n + 1)).Provable φ

/-- Reflection achieves consistency at the same height (modulo shift).
    Provenance: Classical ordinal analysis; deferred for 3B. -/
axiom reflection_height_dominance (T0 : Theory) (φ : Formula) (n : Nat) :
  (LCons T0 n).Provable φ → (LReflect T0 n).Provable φ ∨ ∃ m ≤ n, (LReflect T0 m).Provable φ

end Ax

-- Export for compatibility
export Ax (collision_tag collision_step_semantic reflection_dominates_consistency_axiom
          reflection_height_dominance)

/-! ## Collision Theorems -/

/-- The formal collision: R_{n+1} ⊢ Con(R_n) at the schematic level. -/
theorem collision_step (T0 : Theory) (n : Nat) :
  (LReflect T0 (n+1)).Provable (consFormula n) := by
  -- definitional: step n+1 adds the RFN tag at stage n
  have hRFN : (LReflect T0 (n+1)).Provable (reflFormula n) :=
    LReflect_proves_RFN T0 n
  -- convert RFN-tag to Con-tag via the collision axiom
  exact collision_tag T0 n hRFN


/-! ## Ladder Morphism -/


/-- The collision morphism: reflection dominates consistency with shift by 1 -/
def reflection_dominates_consistency (T0 : Theory) : 
  LadderMorphism (LReflect T0) (LCons T0) :=
{ map := fun n => n + 1
, preserves := reflection_dominates_consistency_axiom T0 }

/-- Special case: the collision at consistency formulas -/
theorem reflection_proves_consistency (T0 : Theory) (n : Nat) :
  (LReflect T0 (n+1)).Provable (consFormula n) :=
  collision_step T0 n

/-! ## Height Comparison -/

end Papers.P4Meta.ProofTheory