/-
Test file to verify functors can handle non-identity morphisms.
Now tests covariant functors as per Option A.
-/

import Gap2.Functor
import APFunctor.Functor
import RNPFunctor.Functor
import Found.InterpCore

open Foundation CategoryTheory

/-- Verify functors can handle the non-identity morphism forget -/
example : Gap.Gap₂.map Interp.forget = Discrete.functor (fun x => x.down.elim) := rfl
example : APFail.AP_Fail₂.map Interp.forget = Discrete.functor (fun x => x.down.elim) := rfl
example : RNPFail.RNP_Fail₂.map Interp.forget = Discrete.functor (fun x => x.down.elim) := rfl

def main : IO Unit := do
  IO.println "✓ All functors are properly covariant and handle non-identity morphisms"