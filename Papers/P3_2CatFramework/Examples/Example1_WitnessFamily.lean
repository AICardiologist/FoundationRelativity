/-
  Example 1: Witness Family Heights (assumption-parametric)
  
  This example shows how to work with witness families and their heights
  on different axes in the AxCal framework.
  
  Compiles cleanly with 0 sorries and introduces no axioms.
-/

import Papers.P3_2CatFramework.Paper3A_Main

namespace Papers.P3.Examples

open Papers.P3.Phase2

/-- Example: The bidual gap as a witness family -/
def GapWitness : WitnessFamily := {
  C := fun _ => Type  -- Placeholder for actual bidual gap property
  size := fun _ => 1  -- Single witness needed
}

/-- Example: Uniform Continuity Theorem (UCT) as a witness family -/
def UCTWitness : WitnessFamily := {
  C := fun _ => Type  -- Placeholder for UCT statement
  size := fun _ => 1
}

section HeightDemonstration
-- Treat these as inputs to the demo (no proof obligations here)
variable
  (h_gap_WLPO : HeightAt WLPO_axis GapWitness = some 1)
  (h_gap_FT   : HeightAt FT_axis GapWitness = some 0)
  (h_uct_WLPO : HeightAt WLPO_axis UCTWitness = some 0)
  (h_uct_FT   : HeightAt FT_axis UCTWitness = some 1)

/-- Bundle the orthogonal profile of Gap: (1,0) -/
def GapProfile : Prop := 
  (HeightAt WLPO_axis GapWitness = some 1) ∧
  (HeightAt FT_axis GapWitness = some 0)

/-- Bundle the orthogonal profile of UCT: (0,1) -/
def UCTProfile : Prop := 
  (HeightAt WLPO_axis UCTWitness = some 0) ∧
  (HeightAt FT_axis UCTWitness = some 1)

/-- Demonstration that Gap has profile (1,0) -/
def gapProfileDemo : GapProfile := 
  And.intro h_gap_WLPO h_gap_FT

/-- Demonstration that UCT has profile (0,1) -/
def uctProfileDemo : UCTProfile := 
  And.intro h_uct_WLPO h_uct_FT

-- Runtime checks to verify the API
#check h_gap_WLPO
#check h_gap_FT
#check gapProfileDemo
#check uctProfileDemo

end HeightDemonstration

#eval "Example 1: Witness families demonstrate orthogonal height profiles"

end Papers.P3.Examples