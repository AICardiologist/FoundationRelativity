/-
  File: Tests/DCw_Frontier_Sanity.lean

  Purpose:
  - Micro-tests for the DCω frontier infrastructure
  - Verify reduction packaging and height lifting work correctly
  - Uses HeightCert := id to avoid framework-specific instances
-/
import Papers.P3_2CatFramework.P4_Meta.DCw_Frontier

namespace Tests
open Papers.P4Meta

section
  -- Toy props so the file is completely self-contained
  variable (DCw Baire : Prop)
  variable (dcw_to_baire : DCw → Baire)

  -- Height certificates as identity (Prop → Prop)
  def HeightCert : Prop → Prop := id
  def height_mono_id : ∀ {P Q}, (P → Q) → HeightCert P → HeightCert Q := fun imp h => imp h

  -- Check the ReducesTo wrapper typechecks
  #check (Papers.P4Meta.DCw_to_Baire_red (DCw := DCw) (Baire := Baire)
         (DCw_to_Baire := dcw_to_baire))

  -- Check the height lifter typechecks and can be used
  #check (Papers.P4Meta.Baire_height1 (DCw := DCw) (Baire := Baire)
          (DCw_to_Baire := dcw_to_baire)
          (HeightCert := HeightCert) height_mono_id :
          HeightCert DCw → HeightCert Baire)

  example (h : HeightCert DCw) :
      HeightCert Baire :=
    (Papers.P4Meta.Baire_height1
      (DCw := DCw) (Baire := Baire) (DCw_to_Baire := dcw_to_baire)
      (HeightCert := HeightCert) height_mono_id) h
end

end Tests