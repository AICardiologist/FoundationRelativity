import Gap2.Functor
import APFunctor.Functor
import RNPFunctor.Functor
import Found.WitnessCore

/-!
# All Pathologies Migration Test
Validates that all three pathology functors have been successfully migrated to use Found.WitnessCore API.
-/

open Foundation CategoryTheory Found

section WitnessTypes
-- Test that witness types are correct for all pathologies
example : WitnessType Gap.Gap₂Pathology bish = Empty := rfl
example : WitnessType Gap.Gap₂Pathology zfc = PUnit := rfl

example : WitnessType APFail.APPathology bish = Empty := rfl
example : WitnessType APFail.APPathology zfc = PUnit := rfl

example : WitnessType RNPFail.RNPPathology bish = Empty := rfl
example : WitnessType RNPFail.RNPPathology zfc = PUnit := rfl
end WitnessTypes

section FunctorEquality
-- Test that functors equal the generic pathologyFunctor
example : Gap.Gap₂ = pathologyFunctor Gap.Gap₂Pathology := rfl
example : APFail.AP_Fail₂ = pathologyFunctor APFail.APPathology := rfl
example : RNPFail.RNP_Fail₂ = pathologyFunctor RNPFail.RNPPathology := rfl
end FunctorEquality

section MorphismHandling
-- Test that all functors handle morphisms correctly
example : Gap.Gap₂.map Interp.id_bish = 𝟭 _ := rfl
example : Gap.Gap₂.map Interp.id_zfc = 𝟭 _ := rfl
example : Gap.Gap₂.map Interp.forget = Discrete.functor (fun x => x.down.elim) := rfl

example : APFail.AP_Fail₂.map Interp.id_bish = 𝟭 _ := rfl
example : APFail.AP_Fail₂.map Interp.id_zfc = 𝟭 _ := rfl
example : APFail.AP_Fail₂.map Interp.forget = Discrete.functor (fun x => x.down.elim) := rfl

example : RNPFail.RNP_Fail₂.map Interp.id_bish = 𝟭 _ := rfl
example : RNPFail.RNP_Fail₂.map Interp.id_zfc = 𝟭 _ := rfl
example : RNPFail.RNP_Fail₂.map Interp.forget = Discrete.functor (fun x => x.down.elim) := rfl
end MorphismHandling

def main : IO Unit := do
  IO.println "✓ All pathology functors successfully migrated to WitnessCore API"
  IO.println "  - Gap₂: ✓"
  IO.println "  - AP_Fail₂: ✓"
  IO.println "  - RNP_Fail₂: ✓"