/-
Logic/Reflection.lean
Uses only the two axioms in Logic/ProofTheoryAxioms.lean:
  • diagonal_lemma   : ¬Provable G → (G ↔ ¬Provable G)
  • provable_sound   :  Provable G → False
No other assumptions, no `sorry`.
-/
import Logic.ProofTheoryAxioms

open Arithmetic

namespace Logic

theorem reflection_equiv : (¬ Provable G_formula) ↔ G := by
  -- → :   ¬Provable G  ⇒  G     (diagonal lemma, forward)
  have h₁ : (¬ Provable G_formula) → G := by
    intro h
    exact (diagonal_lemma h).mpr h
  -- ← :   G ⇒ ¬Provable G        (soundness, contrapositive)
  have h₂ : G → ¬ Provable G_formula := by
    intro hG hP
    exact provable_sound hP
  exact ⟨h₁, h₂⟩

end Logic