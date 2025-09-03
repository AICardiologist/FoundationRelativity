/-
  Papers/P3_2CatFramework/Paper3C_Main.lean
  
  Paper 3C: DCω/Baire Axis Calibration
  Main aggregator for Paper 3C components
  
  This aggregates the DCω → Baire infrastructure which establishes
  the third orthogonal axis in the AxCal framework.
  
  Note: Paper 3C was initially split off for separate development
  but is now being reintegrated into Paper 3A. This aggregator
  allows clean import of all Paper 3C components.
-/

-- DCω/Baire axis infrastructure
import Papers.P3_2CatFramework.P4_Meta.DCw_Frontier
-- Note: DCwPortalWire not imported here to avoid conflicts with PartIII_Ladders
-- DCw_Frontier provides the core DCω → Baire reduction functionality

/-! 
## Paper 3C Summary

Paper 3C establishes the DCω (Dependent Choice) axis as the third orthogonal
dimension in the AxCal framework, complementing WLPO and FT axes.

### Key Results:
1. DCω → Baire Category Theorem reduction
2. Height calibration: Baire at height 1 on DCω axis
3. Orthogonal profile: (0, 0, 1) for Baire on (WLPO, FT, DCω) axes

### Infrastructure:
- `DCw_Frontier.lean`: Core DCω → Baire reduction and height transport
- Note: DCwPortalWire and IndependenceRegistry have namespace conflicts
  with PartIII_Ladders and are handled separately in the framework

### Applications (Future Work):
- Uniform Boundedness Principle (UBP)
- Open Mapping Theorem (OMT)
- Closed Graph Theorem (CGT)

These require Baire Category and thus calibrate at height 1 on the DCω axis.
-/

namespace Papers.P3C

-- Re-export key definitions for convenience
open Papers.P4Meta

-- Marker to confirm Paper 3C aggregator loaded
def paper3C_loaded : Bool := true

end Papers.P3C