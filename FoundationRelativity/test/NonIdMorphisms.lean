/-
Test file to verify functors can handle non-identity morphisms.
Now tests covariant functors using the new Witness API.
-/

import Gap2.Functor
import APFunctor.Functor
import RNPFunctor.Functor
import Found.InterpCore
import Found.WitnessCore

open Foundation CategoryTheory

/-- Verify functors handle the non-identity morphism `forget`. -/
example : Gap.Gap₂.map Interp.forget = Discrete.functor (fun x => x.down.elim) := rfl
example : APFail.AP_Fail₂.map Interp.forget = FoundationRelativity.fromEmpty := rfl
example : RNPFail.RNP_Fail₂.map Interp.forget = FoundationRelativity.fromEmpty := rfl

/-- Verify `Gap₂` is built with the new witness API. -/
example : Gap.Gap₂ = Found.pathologyFunctor Gap.Gap₂Pathology := rfl

def main : IO Unit := do
  IO.println "✓ All functors are properly covariant and handle non-identity morphisms"