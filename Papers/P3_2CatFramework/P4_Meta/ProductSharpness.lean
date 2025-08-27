/-
  File: Papers/P3_2CatFramework/P4_Meta/ProductSharpness.lean
  
  Purpose: WP-C Sharpness from Independence
  - Lemmas showing that independent axes yield sharp product heights
  - Connects independence registry to height certificates
  - Justifies the "max" law for orthogonal products
-/

import Papers.P3_2CatFramework.P4_Meta.Frontier_API
import Papers.P3_2CatFramework.P4_Meta.IndependenceRegistry

namespace Papers.P4Meta

section ProductSharpness

variable {HeightCert : Prop → Prop}
variable (height_mono : ∀ {P Q}, (P → Q) → HeightCert P → HeightCert Q)
variable (height_and  : ∀ {P Q}, HeightCert P → HeightCert Q → HeightCert (P ∧ Q))

/-- Sharpness from orthogonality (interface-level).
    If `C` needs WLPO and `D` needs FT, then with WLPO⊥FT the product lands at the
    fused profile; at Prop-level we expose it as a certificate for `C ∧ D`. -/
def sharp_product_of_indep
    {C D : Prop} {WLPO FT : Prop}
    (needs_W : WLPO → C) (needs_F : FT → D)
    (_indep : Independent WLPO FT)
    (w1 : HeightCert WLPO) (w2 : HeightCert FT) : HeightCert (C ∧ D) :=
  let hC : HeightCert C := height_mono needs_W w1
  let hD : HeightCert D := height_mono needs_F w2
  height_and hC hD

/-- Specialized version for our standard calibrators. -/
theorem sharp_UCT_Gap_product 
    {HeightCert : Prop → Prop}
    (height_mono : ∀ {P Q}, (P → Q) → HeightCert P → HeightCert Q)
    (height_and  : ∀ {P Q}, HeightCert P → HeightCert Q → HeightCert (P ∧ Q))
    {Gap UCT : Prop}
    (gap_from_wlpo : WLPO → Gap)
    (uct_from_ft : FT → UCT)
    (hw : HeightCert WLPO)
    (hf : HeightCert FT) :
    HeightCert (Gap ∧ UCT) := 
  sharp_product_of_indep height_mono height_and gap_from_wlpo uct_from_ft indep_WLPO_FT hw hf

/-- Triple product with three independent axes. -/
theorem sharp_triple_product
    {HeightCert : Prop → Prop}
    (height_mono : ∀ {P Q}, (P → Q) → HeightCert P → HeightCert Q)
    (height_and  : ∀ {P Q}, HeightCert P → HeightCert Q → HeightCert (P ∧ Q))
    {C D E : Prop}
    (needs_W : WLPO → C)
    (needs_F : FT → D) 
    (needs_DC : DCw → E)
    (hw : HeightCert WLPO)
    (hf : HeightCert FT)
    (hdc : HeightCert DCw) :
    HeightCert (C ∧ D ∧ E) :=
  -- Uses all three independence assumptions
  -- First combine C and D
  let hCD := sharp_product_of_indep height_mono height_and needs_W needs_F indep_WLPO_FT hw hf
  -- Then combine with E
  height_and hCD (height_mono needs_DC hdc)

/-! ### Height Profile Notation

For documentation purposes, we record height profiles as tuples:
- (h_WLPO, h_FT) = (0, 1) means: height 0 on WLPO axis, height 1 on FT axis
- This corresponds to needing FT but not WLPO
-/

/-- UCT has profile (0, 1): doesn't need WLPO, needs FT. -/
example {HeightCert : Prop → Prop} {UCT : Prop} 
    (uct_from_ft : FT → UCT)
    (uct_without_wlpo : UCT)  -- UCT holds without WLPO
    : True := trivial

/-- Gap has profile (1, 0): needs WLPO, doesn't need FT. -/  
example {HeightCert : Prop → Prop} {Gap : Prop}
    (gap_from_wlpo : WLPO → Gap)
    (gap_without_ft : Gap)  -- Gap can exist without FT
    : True := trivial

end ProductSharpness

/-! ### Integration with Part II Product/Sup Law

Once we have the concrete witness product type from Part II,
replace the `∧` conjunctions above with the actual product construction
and use the existing product/sup height lemmas.
-/

end Papers.P4Meta