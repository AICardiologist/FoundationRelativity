import Papers.P3_2CatFramework.Paper3A_Main

/-!
  # Paper 3A API: Clean Re-export Interface
  
  This module provides a clean API for Paper 3A components,
  re-exporting the key namespaces for easier consumption.
  
  ## Usage
  ```lean
  import Papers.P3_2CatFramework.Paper3A_API
  ```
  
  This gives you access to:
  - Phase 1: Bicategorical foundations
  - Phase 2: Uniformization and witness families
  - Phase 3: Height theory and levels
  - FT Frontier: Multi-axis calibration
-/

namespace Papers.P3.API

-- Re-export Phase 1: Bicategorical structure
export Papers.P3.Phase1Simple (Foundation Interp TwoCell id_interp comp_interp
  id_2cell vcomp_2cell left_unitor right_unitor associator 
  BISH BISH_WLPO bish_to_wlpo FoundationTwoCategory)

-- Re-export Phase 2: Uniformization theory
export Papers.P3.Phase2 (Sigma0 WitnessFamily UniformizableOn 
  GapFamily hasWLPO W_ge0 W_ge1 Truth
  uniformization_height1 no_uniformization_height0)

-- Re-export Phase 2 API: Height computation
export Papers.P3.Phase2API (Level HeightAt satisfiesLevel
  getUniformizationAt gap_has_height_one 
  HeightAtNat_viaPhase2 HeightAt_viaNat)

-- Re-export Phase 3: Numeric levels
export Papers.P3.Phase3 (W_ge UniformizableOnN HeightAtNat
  toW0 toW1 gap_height_nat_is_one)

-- Re-export FT Frontier: Multi-axis theory
export Papers.P3.FTFrontier (Axis WLPO_axis FT_axis HeightOracle
  AxCalProfile getProfile UCTWitness
  gap_orthogonal_profile uct_orthogonal_profile axes_independent)

end Papers.P3.API

/-!
## Quick Reference

### Core Types
- `Foundation`: Mathematical foundation with WLPO bit
- `WitnessFamily`: Indexed collection of witnesses
- `HeightOracle`: Assumption-parametric height assignment
- `AxCalProfile`: 2D height profile (WLPO × FT)

### Key Functions
- `HeightAt`: Compute uniformization height
- `getProfile`: Extract 2D profile from oracle

### Main Theorems
- `gap_has_height_one`: Bidual gap at height 1
- `axes_independent`: WLPO and FT axes are orthogonal
-/