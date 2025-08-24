/-
  Papers/P3_2CatFramework/test/Positive_Pins_test.lean
  Sanity checks for pins-aware positive uniformization
-/
import Papers.P3_2CatFramework.Phase2_PositivePins

open Papers.P3.Phase2
open Papers.P3.Phase2Positive

namespace Papers.P3.Tests

-- Constant predicate families for truth-families tests
def B_true  : Foundation → Sigma0 → Bool := fun _ _ => true
def B_false : Foundation → Sigma0 → Bool := fun _ _ => false

-- All-pins positivity for 'true' (re-uses the truth characterization)
example (W : Foundation → Prop) :
  PosUniformizableOn W (TruthFamily B_true) :=
  (posUL_truth_iff (W := W) (B := B_true)).2 (by intro F hF X; rfl)

-- Pins-aware positivity follows from all-pins positivity (singleton pin {nat})
example (W : Foundation → Prop) :
  PosUniformizableOnPins W (TruthFamily B_true) ({Sigma0.nat} : Set Sigma0) :=
  (PosUniformizableOn.toPins (S := ({Sigma0.nat} : Set Sigma0)))
    ((posUL_truth_iff (W := W) (B := B_true)).2 (by intro F hF X; rfl))

-- Equivalence on univ pins ↔ old notion
example (W : Foundation → Prop) :
  (PosUniformizableOnPins W (TruthFamily B_true) Set.univ)
    ↔ PosUniformizableOn W (TruthFamily B_true) :=
  PosUniformizableOn_univ

-- Constant-false cannot be positively uniformized on a nonempty locus, even on one pin
example (W : Foundation → Prop) (hW : ∃ F, W F) :
  ¬ PosUniformizableOnPins W (TruthFamily B_false) ({Sigma0.nat} : Set Sigma0) := by
  intro h
  -- Use the pins-aware truth characterization
  have h' := (posUL_truth_on_iff (W := W) (B := B_false)
               (S := ({Sigma0.nat} : Set Sigma0))).1 h
  rcases hW with ⟨F, hF⟩
  -- Specialize at the chosen pin (nat ∈ {nat})
  have : false = true := h'.2 hF (X := Sigma0.nat) rfl
  simp at this

#eval IO.println "Positive_Pins tests: OK!"

end Papers.P3.Tests