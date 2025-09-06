import Papers.P3C_DCwAxis.DCw_Frontier_Interface
import Papers.P3C_DCwAxis.DCw_Baire
import Papers.P3_2CatFramework.P4_Meta.DCw_Frontier

/-!
  # Paper 3C: DC_ω Axis Calibration
  
  Main aggregator for Paper 3C components.
  This establishes the third orthogonal axis of the AxCal framework.
  
  ## Status: Early Development
  
  ## Components
  - DC_ω principle definition
  - Baire space formalization (ℕ^ℕ with product topology)
  - DC_ω → Baire proof skeleton
  - Height calibration on third axis
-/

namespace Papers.P3C

-- Re-export tokens for convenience
export Papers.P3C.DCw (DCω BaireNN BaireFromDCωStatement baireNN_of_DCω)

/-!
## Summary

Paper 3C establishes that:
1. DC_ω implies BaireSpace(ℕ → ℕ)
2. This gives a third calibration axis
3. Profile: (WLPO, FT, DC_ω) = (0, 0, 1)

The proof uses the standard reverse mathematics argument:
- Given dense opens, use DC_ω to build nested closed cylinders
- The intersection yields the required function
-/

end Papers.P3C