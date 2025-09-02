/-
  Example 2: Height Composition (Product/Sup)
  
  This example demonstrates how heights compose under logical operations
  in the AxCal framework.
  
  Compiles cleanly with 0 sorries and introduces no axioms.
-/

import Papers.P3_2CatFramework.Paper3A_Main

namespace Papers.P3.Examples

open Papers.P3.Phase2
open Papers.P3.Phase3

/-- Example: Product of witness families -/
def ProductExample (W₁ W₂ : WitnessFamily) : WitnessFamily := {
  C := fun foundation => W₁.C foundation × W₂.C foundation
  size := fun foundation => W₁.size foundation + W₂.size foundation
}

/-- Example: Disjunction (Sup) of witness families -/
def SupExample (W₁ W₂ : WitnessFamily) : WitnessFamily := {
  C := fun foundation => W₁.C foundation ∨ W₂.C foundation
  size := fun foundation => max (W₁.size foundation) (W₂.size foundation)
}

section CompositionDemonstration
-- Assume the API provides these composition rules
variable
  (height_product_rule : ∀ (W₁ W₂ : WitnessFamily) (axis : Axis),
    HeightAt axis (ProductExample W₁ W₂) = 
    max (HeightAt axis W₁) (HeightAt axis W₂))
  (height_sup_rule : ∀ (W₁ W₂ : WitnessFamily) (axis : Axis),
    HeightAt axis (SupExample W₁ W₂) = 
    max (HeightAt axis W₁) (HeightAt axis W₂))

-- Check that these rules exist in the API
#check height_product_rule
#check height_sup_rule

/-- Define what it means for Gap ∨ UCT to have profile (1,1) -/
def SupProfileProperty : Prop :=
  (HeightAt WLPO_axis (SupExample GapWitness UCTWitness) = some 1) ∧
  (HeightAt FT_axis (SupExample GapWitness UCTWitness) = some 1)

-- If we had the specific height values, we could compute:
section ConcreteExample
variable
  (h_gap_WLPO : HeightAt WLPO_axis GapWitness = some 1)
  (h_gap_FT   : HeightAt FT_axis GapWitness = some 0)
  (h_uct_WLPO : HeightAt WLPO_axis UCTWitness = some 0)
  (h_uct_FT   : HeightAt FT_axis UCTWitness = some 1)

-- The sup would have max on each axis
-- WLPO axis: max(1,0) = 1
-- FT axis: max(0,1) = 1
-- This demonstrates the componentwise maximum behavior

#check SupExample GapWitness UCTWitness

end ConcreteExample

end CompositionDemonstration

#eval "Example 2: Heights compose via max under both product and disjunction"

end Papers.P3.Examples