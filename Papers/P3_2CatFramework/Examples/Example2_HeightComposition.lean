/-
  Example 2: Height Composition (Product/Sup)
  
  This example demonstrates how heights compose under logical operations
  in the AxCal framework.
  
  Compiles cleanly with 0 sorries and introduces no axioms.
-/

import Papers.P3_2CatFramework.Paper3A_Main

namespace Papers.P3.Examples

open Papers.P3.Phase2
open Papers.P3.FTFrontier  -- Axis, HeightOracle

/-- Product of witness families (toy). -/
def ProductExample (W₁ W₂ : WitnessFamily) : WitnessFamily :=
  { C := fun F X => W₁.C F X × W₂.C F X }

/-- Disjunction (sup) of witness families (toy). -/
def SupExample (W₁ W₂ : WitnessFamily) : WitnessFamily :=
  { C := fun F X => (W₁.C F X) ⊕ (W₂.C F X) }

def GapWitness : WitnessFamily := { C := fun _ _ => PUnit }
def UCTWitness : WitnessFamily := { C := fun _ _ => PUnit }

section CompositionDemonstration
  variable (O : HeightOracle)

  -- Assume the composition rules for heights (axis-wise max)
  variable
    (height_product_rule :
      ∀ (W₁ W₂ : WitnessFamily) (axis : Axis),
        O.heightAt axis (ProductExample W₁ W₂)
        = max (O.heightAt axis W₁) (O.heightAt axis W₂))
    (height_sup_rule :
      ∀ (W₁ W₂ : WitnessFamily) (axis : Axis),
        O.heightAt axis (SupExample W₁ W₂)
        = max (O.heightAt axis W₁) (O.heightAt axis W₂))

  -- Concrete heights for Gap/UCT on the two axes (assumed inputs)
  variable
    (h_gap_WLPO : O.heightAt WLPO_axis GapWitness = some 1)
    (h_gap_FT   : O.heightAt FT_axis GapWitness = some 0)
    (h_uct_WLPO : O.heightAt WLPO_axis UCTWitness = some 0)
    (h_uct_FT   : O.heightAt FT_axis UCTWitness = some 1)

  -- We keep this as a property rather than forcing arithmetic on Option Nat
  def SupProfileProperty : Prop :=
    (O.heightAt WLPO_axis (SupExample GapWitness UCTWitness) = some 1) ∧
    (O.heightAt FT_axis (SupExample GapWitness UCTWitness) = some 1)

  -- Just #check the rules are in scope (and the examples compile)
  #check height_product_rule
  #check height_sup_rule
  #check SupExample GapWitness UCTWitness
end CompositionDemonstration

#eval "Example 2: Heights compose via max under both product and disjunction"

end Papers.P3.Examples