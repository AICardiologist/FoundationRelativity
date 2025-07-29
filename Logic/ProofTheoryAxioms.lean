/-
Logic/ProofTheoryAxioms.lean

Minimal axioms for proof theory needed to prove reflection_equiv.
These are placeholders until full proof theory is implemented.
-/

import Papers.P1_GBC.Arithmetic

namespace Arithmetic

/-- The Gödel sentence G -/
def G : Prop := ¬ Provable G_formula

/-- Diagonal lemma: G is equivalent to "G is not provable" -/
axiom diagonal_lemma : ∀ (h : ¬ Provable G_formula), G ↔ ¬ Provable G_formula

/-- Soundness: If G is provable, then G is false -/
axiom provable_sound : Provable G_formula → ¬ G

end Arithmetic