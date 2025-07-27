import CategoryTheory.BicatHelpers

open CategoryTheory.BicatFound

/-- Register basic 2‑cell simplifications for bicategory automation. -/
attribute [simp] id_2cell vcomp_2cell hcomp_2cell

/-- Register Inv₂ simplifications for automated reasoning. -/
attribute [simp] Inv₂.left Inv₂.right

-- TODO Day 3: Math-AI can extend this with pentagon/triangle automation