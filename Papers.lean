/-
  Papers.lean - Main Papers coordination
  
  Paper formalization modules for Foundation-Relativity project.
  
  Structure:
  - P1_GBC: Rank-One Toggle Kernel (Sherman-Morrison implementation + stubs)
  - P2_BidualGap: WLPO ↔ BidualGap equivalence (dual isometry complete)
  - P3_2CatFramework: 2-categorical foundation-relativity framework
  - P4_SpectralGeometry: Undecidable eigenvalue problems on manifolds
  
  Note: Individual minimal modules are built as separate executables.
  This provides coordination and documentation for all papers.
-/

-- Import active paper modules (no legacy dependencies)
import Papers.P1_GBC.P1_Minimal
import Papers.P2_BidualGap.P2_Minimal
import Papers.P3_2CatFramework
-- Papers.P4_SpectralGeometry modules available but not imported for faster builds

namespace Papers

/-! ### Papers Coordination -/

-- Documentation and coordination between active paper implementations
-- Each paper has validated smoke tests and minimal builds