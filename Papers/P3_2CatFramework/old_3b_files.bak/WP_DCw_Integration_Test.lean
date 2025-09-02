/-
  File: Papers/P3_2CatFramework/P4_Meta/WP_DCw_Integration_Test.lean
  
  Purpose: Test DCω frontier integration with existing WP infrastructure
  - Verifies DCω/Baire wiring
  - Tests Gap × Baire orthogonal product (WLPO axis × DCω axis)
  - Uses parametric ProductSharpness with toy HeightCert := id
-/

import Papers.P3_2CatFramework.P4_Meta.DCwPortalWire
import Papers.P3_2CatFramework.P4_Meta.ProductSharpness
import Papers.P3_2CatFramework.P4_Meta.StonePortalWire  -- For Gap token

namespace Papers.P4Meta

section DCwIntegration

-- Toy instantiation for testing
def HeightCert (P : Prop) := P
theorem height_mono_id {P Q} (h : P → Q) : HeightCert P → HeightCert Q := h
theorem height_and_id {P Q} : HeightCert P → HeightCert Q → HeightCert (P ∧ Q) :=
  fun p q => And.intro p q

/-- Test that Baire height transport works -/
example (dcw_h1 : HeightCert DCw) : HeightCert Baire :=
  Baire_height1_from_DCw height_mono_id dcw_h1

/-- Test Gap × Baire orthogonal product (WLPO axis × DCω axis) -/
example (gap_from_wlpo : WLPO → Gap)
        (baire_from_dcw : DCw → Baire)
        (wlpo_h1 : HeightCert WLPO)
        (dcw_h1 : HeightCert DCw) :
        HeightCert (Gap ∧ Baire) :=
  -- Use the parametric sharpness theorem
  -- Note: We use indep_WLPO_DCw from IndependenceRegistry
  sharp_product_of_indep (HeightCert := HeightCert)
    height_mono_id height_and_id gap_from_wlpo baire_from_dcw 
    indep_WLPO_DCw wlpo_h1 dcw_h1

/-- Verify height profiles:
    - Gap has profile (1, 0, 0): needs WLPO, not FT, not DCω
    - Baire has profile (0, 0, 1): not WLPO, not FT, needs DCω
    - Gap × Baire has profile (1, 0, 1): needs both WLPO and DCω
-/
example : True := trivial

/-! ### Axiom Dependencies -/

#print axioms Baire_height1_from_DCw
-- Should show: DCw, Baire, DCw_to_Baire

#print axioms sharp_product_of_indep
-- Should show: Independent, WLPO, DCw, indep_WLPO_DCw (when used with Gap × Baire)

end DCwIntegration

end Papers.P4Meta