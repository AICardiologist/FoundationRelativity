/-
Axiom for now; Day‑4 drop will supply a proof.
-/
import Papers.P1_GBC.Defs
import Papers.P1_GBC.Core

namespace Logic
open Papers.P1_GBC.Defs Papers.P1_GBC.Core

axiom reflection_equiv :
  consistencyPredicate peanoArithmetic ↔ GödelSentenceTrue

end Logic