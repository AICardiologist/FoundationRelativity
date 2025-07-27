import CategoryTheory.BicatFound

/-!
# Miscellaneous helpers for bicategorical algebra
These will be imported by `PseudoFunctor.lean` and instance files.
-/

open CategoryTheory.BicatFound

/-- An *invertible 2‑cell* between 1‑cells `f` and `g`. -/
structure Inv₂ {A B : Foundation} (f g : Interp A B) where
  α     : BicatFound_TwoCell f g
  inv   : BicatFound_TwoCell g f
  left  : vcomp_2cell α inv = id_2cell f
  right : vcomp_2cell inv α = id_2cell g

attribute [simp] Inv₂.left Inv₂.right