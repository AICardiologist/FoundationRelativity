/-
  Papers/P4_Meta/PartV_Smoke_test.lean
  
  Smoke tests for Part V collision theorems and Stone window.
-/
import Papers.P3_2CatFramework.P4_Meta.PartV_Strictness
import Papers.P3_2CatFramework.P4_Meta.StoneWindow

namespace Papers.P4Meta.Tests

open Papers.P4Meta
open Papers.P4Meta.PartV
open Papers.P4Meta.StoneWindow

-- Test that we can instantiate a theory with the required typeclasses
def TestTheory : Theory := Paper3Theory

-- We need instances for the test theory
instance : HBL TestTheory := ⟨trivial⟩
instance : RE TestTheory := ⟨trivial⟩
instance : CodesProofs TestTheory := {
  encode_proof := fun _ _ => 0
  decode_valid := fun φ _ _ => trivial
}
instance : Sigma1Sound TestTheory where
  reflection_holds := by
    intros phi _
    -- Extend preserves the "always true" property
    simp only [Extend, TestTheory, Paper3Theory]
    left
    trivial

-- Test the collision chain compiles
example : (Extend (Extend TestTheory (RFN_Sigma1 TestTheory)) 
           (Con TestTheory)).Provable (GodelSentence TestTheory) :=
  collision_chain TestTheory

-- Test Stone window Boolean operations
example : BoolSeq.zero + BoolSeq.zero = BoolSeq.zero :=
  rfl

example (f : BoolSeq) : f + f = BoolSeq.zero :=
  BoolSeq.add_self f

-- Test finite support ideal
def emptyPred : Nat → Prop := fun _ => False
def finitePred : Nat → Prop := fun n => n = 1 ∨ n = 2 ∨ n = 3

example : IsFinite emptyPred := by
  refine ⟨0, ?_⟩
  intros _ hm
  cases hm

example : IsFinite finitePred := by
  refine ⟨4, ?_⟩
  intros n hn
  cases hn with
  | inl h => rw [h]; decide
  | inr h => cases h with
    | inl h => rw [h]; decide 
    | inr h => rw [h]; decide

#eval "Part V smoke tests: OK!"

end Papers.P4Meta.Tests