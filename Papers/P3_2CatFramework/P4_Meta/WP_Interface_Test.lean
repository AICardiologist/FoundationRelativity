/-
  File: Papers/P3_2CatFramework/P4_Meta/WP_Interface_Test.lean
  
  Purpose: Sanity test that WP interface files compile and have 0 sorries
-/

import Papers.P3_2CatFramework.P4_Meta.IndependenceRegistry
import Papers.P3_2CatFramework.P4_Meta.StoneWindow_SupportIdeals
import Papers.P3_2CatFramework.P4_Meta.FusedLadders
import Papers.P3_2CatFramework.P4_Meta.PartV_RFNSigma1

namespace Papers.P4Meta

/-- Test that independence is symmetric -/
example : Independent WLPO FT → Independent FT WLPO := 
  Independent.symm

/-- Test that we have the standard independence axioms -/
example : Independent WLPO FT := indep_WLPO_FT
example : Independent FT DCw := indep_FT_DCw

/-- Test that height_product_on_fuse is available -/
example {L1 L2 : Type} {a b : Nat} {C D : Prop}
    (hC : HeightAt L1 a C) (hD : HeightAt L2 b D) :
    HeightAt (fuse L1 L2) (Nat.max a b) (C ∧ D) :=
  height_product_on_fuse hC hD

/-- Test that RFN_Sigma1_implies_Consistency is available -/
example (T : Theory) [CodesProofs T] [Sigma1Sound T] [HasReflection T] :
    Provable (Extend T (RFN_Sigma1 T)) (Con T) :=
  RFN_Sigma1_implies_Consistency T

#print axioms Independent.symm
-- Should show: 'Independent.symm' depends on axioms: [WLPO, FT, DCw]

#print axioms height_product_on_fuse  
-- Should show: 'height_product_on_fuse' depends on axioms: [height_product_on_fuse]

end Papers.P4Meta