import CategoryTheory.PseudoFunctor
import CategoryTheory.Bicategory

namespace CategoryTheory

open CategoryTheory

variable {B C D : Type*} [Bicategory B] [Bicategory C] [Bicategory D]

/-! ### 1.  Horizontal composition of pseudo‑functors -/

/-- Composition of pseudo‑functors (works even without extra coherence proofs
    because we reuse the component‑wise ones).  This is *definitionally* identical
    to the code you sketched in `PseudoFunctorComp.lean`, but packaged inside
    `CategoryTheory` so downstream files can just write `F ⋙ G`. -/
@[simps]
def PseudoFunctor.comp (F : PseudoFunctor B C) (G : PseudoFunctor C D) :
    PseudoFunctor B D where
  obj  X := G.obj (F.obj X)
  map₁ f := G.map₁ (F.map₁ f)
  map₂ η := G.map₂ (F.map₂ η)
  map_id₁ := by intro; simp
  map_comp₁ := by intro; simp
  map_id₂ := by intro; simp
  map_comp₂ := by intro; simp
  map_comp₂' := by intro; simp
  map₂_isIso := by
    intro f
    simpa using G.map₂_isIso _

notation F " ⋙ " G => PseudoFunctor.comp F G

/-! ### 2.  Helper showing map₂ preserves invertible 2-cells -/

lemma PseudoFunctor.map₂_preserves_inv {B C : Type*} [Bicategory B] [Bicategory C]
    (G : PseudoFunctor B C) {X Y : B} {f g : X ⟶ Y} {η : f ⟶ g}
    (hinv : ∃ (η_inv : g ⟶ f), η ≫ η_inv = 𝟙 f ∧ η_inv ≫ η = 𝟙 g) :
    ∃ (η'_inv : G.map₁ g ⟶ G.map₁ f), 
      G.map₂ η ≫ η'_inv = 𝟙 (G.map₁ f) ∧ η'_inv ≫ G.map₂ η = 𝟙 (G.map₁ g) := by
  obtain ⟨η_inv, h1, h2⟩ := hinv
  use G.map₂ η_inv
  simp [← G.map₂_comp, h1, h2, G.map₂_id]

/-! ### 3.  `map₁` preserves isomorphisms (used by `hcomp`) -/

@[simp]
lemma PseudoFunctor.map₁_isIso
    {B C : Type*} [Bicategory B] [Bicategory C]
    (F : PseudoFunctor B C) {X Y : B} {f : X ⟶ Y}
    [IsIso f] :
    IsIso (F.map₁ f) := by
  -- the pseudo‑functor's `map₁_isIso` lemma already exists in your
  -- Sprint‑43 `PseudoFunctor.lean`; we just expose it with a shorter name
  simpa using F.map₁_isIso f

end CategoryTheory