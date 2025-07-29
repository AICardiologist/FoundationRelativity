/-
Logic/ProofTheoryAxioms.lean

Minimal axioms for proof theory needed to prove reflection_equiv.
These are placeholders until full proof theory is implemented.
-/

import Papers.P1_GBC.Arithmetic
import Papers.P1_GBC.Defs

namespace Arithmetic

/-- The Gödel sentence G -/
def G : Prop := ¬ Provable G_formula

/-- Diagonal lemma: G is equivalent to "G is not provable" -/
axiom diagonal_lemma : ¬ Provable G_formula → (G ↔ ¬ Provable G_formula)

/-- Soundness: If G is provable, then G is false -/
axiom provable_sound : Provable G_formula → False

/-- Helper: If something is unprovable, PA must be consistent -/
axiom consistency_from_unprovability :
  ¬Provable G_formula → Papers.P1_GBC.Defs.consistencyPredicate Papers.P1_GBC.Defs.peanoArithmetic

end Arithmetic