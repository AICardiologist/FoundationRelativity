/-
  Example 1: Witness Family Heights (assumption-parametric)
  
  This example shows how to work with witness families and their heights
  on different axes in the AxCal framework.
  
  Compiles cleanly with 0 sorries and introduces no axioms.
-/

import Papers.P3_2CatFramework.Paper3A_Main

namespace Papers.P3.Examples

open Papers.P3.Phase2
open Papers.P3.FTFrontier  -- bring in Axis, WLPO_axis, FT_axis, HeightOracle, getProfile

section HeightDemonstration
  -- Use an oracle to demonstrate heights without axioms
  variable (O : HeightOracle)
  
  /-- Gap has orthogonal profile (1,0) under the standard oracle. -/
  theorem gap_profile_demo : 
    getProfile O GapFamily = ⟨some 1, some 0⟩ := by
    simp [getProfile, O.gap_wlpo, O.gap_ft]

  /-- UCT has orthogonal profile (0,1) under the standard oracle. -/
  theorem uct_profile_demo : 
    getProfile O UCTWitness = ⟨some 0, some 1⟩ := by
    simp [getProfile, O.uct_wlpo, O.uct_ft]

  /-- We can demonstrate orthogonality without axioms. -/
  theorem orthogonality_demo (O : HeightOracle) :
    (getProfile O GapFamily).wlpo_height = some 1 ∧
    (getProfile O GapFamily).ft_height = some 0 ∧
    (getProfile O UCTWitness).wlpo_height = some 0 ∧
    (getProfile O UCTWitness).ft_height = some 1 := by
    simp [getProfile, O.gap_wlpo, O.gap_ft, O.uct_wlpo, O.uct_ft]

  -- Sanity checks
  #check gap_profile_demo
  #check uct_profile_demo
  #check orthogonality_demo
end HeightDemonstration

#eval "Example 1: Witness families demonstrate orthogonal height profiles"

end Papers.P3.Examples