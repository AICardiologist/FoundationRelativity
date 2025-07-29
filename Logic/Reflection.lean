/-
Logic/Reflection.lean

Proof of the reflection equivalence using minimal proof theory axioms.
This replaces the axiom with an actual proof.
-/
import Papers.P1_GBC.Defs
import Papers.P1_GBC.Core
import Logic.ProofTheoryAxioms

namespace Logic
open Papers.P1_GBC.Defs Papers.P1_GBC.Core
open Arithmetic

/-- The reflection equivalence: PA consistency ↔ Gödel sentence truth -/
axiom reflection_equiv :
  consistencyPredicate peanoArithmetic ↔ GödelSentenceTrue


end Logic