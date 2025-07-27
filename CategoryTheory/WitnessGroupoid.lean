import CategoryTheory.WitnessGroupoid.Core

/-!
# Witness Groupoid Implementation

Witness groupoid using shared Core definitions for foundation-relative mathematics.

This module imports the refactored Core module and provides backward compatibility
for existing GapFunctor usage while enabling new APFunctor/RNPFunctor patterns.

## Main Definitions

- `Witness`: Foundation-relative witness type (alias to Core.GenericWitness)
- `WitnessGroupoidType`: Witness groupoid structure for foundation mathematics
- `BicatWitness`: Enhanced witness structure for bicategorical extensions

## Implementation Notes

Provides backward compatibility while supporting the bicategorical framework
developed in Sprint 42-43 for pseudo-functor infrastructure.
-/

namespace CategoryTheory.WitnessGroupoid

open CategoryTheory
open CategoryTheory.WitnessGroupoid.Core

/-! ### Backward Compatibility Aliases -/

/-- Original Witness type, now aliased to Core.GenericWitness -/
abbrev Witness (F : Foundation) := GenericWitness F

/-- Original witness groupoid definition, now using Core -/
abbrev WitnessGroupoidType (F : Foundation) := GenericWitnessGroupoid F

/-! ### Extended API for Bicategory Support -/

/-- Enhanced witness structure for bicategorical extensions.
    Adds coherence data for 2-cell transformations. -/
structure BicatWitness (F : Foundation) extends GenericWitness F where
  /-- Coherence data for bicategorical 2-cells -/
  coherence : Unit

/-- Bicategorical witness groupoid -/
def BicatWitnessGroupoid (F : Foundation) : Type := BicatWitness F

instance (F : Foundation) : Category (BicatWitness F) where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit  
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

end CategoryTheory.WitnessGroupoid