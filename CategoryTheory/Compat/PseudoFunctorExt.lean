import CategoryTheory.PseudoFunctor
import CategoryTheory.Bicategory   -- you already had this

open CategoryTheory Bicategory

variable {B C D : Type*} [Bicategory B] [Bicategory C] [Bicategory D]

namespace CategoryTheory

/-! ### 1  Composition of pseudo‑functors -/

@[simps]
def PseudoFunctor.comp (F : PseudoFunctor B C) (G : PseudoFunctor C D) :
    PseudoFunctor B D where
  obj  X := G.obj (F.obj X)
  map₁ f := G.map₁ (F.map₁ f)
  map₂ η := G.map₂ (F.map₂ η)
  map_id₁   := by intro; simp
  map_comp₁ := by intro; simp
  map_id₂   := by intro; simp
  map_comp₂ := by intro; simp
  map_comp₂':= by intro; simp
  map₂_isIso := by
    intro f
    simpa using G.map₂_isIso (F.map₂ f)

notation F " ⋙ " G => PseudoFunctor.comp F G

/-! ### 2  Helper: `map₁` preserves isomorphisms -/
@[simp]
lemma PseudoFunctor.map₁_isIso
    (F : PseudoFunctor B C) {X Y : B} {f : X ⟶ Y} [IsIso f] :
    IsIso (F.map₁ f) := by
  simpa using F.map₁_isIso f

end CategoryTheory