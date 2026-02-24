/-
  Papers.lean - Main Papers coordination

  Constructive Reverse Mathematics Series — 70-paper programme.
  Lean 4 formalization bundles for active papers.

  Structure:
  - P2_BidualGap: WLPO ↔ BidualGap equivalence
  - P4_SpectralGeometry: Quantum spectra axiom calibration
  - P5_GeneralRelativity: Schwarzschild curvature verification
  - P6_Heisenberg_v2: Heisenberg uncertainty principle

  Note: Most paper bundles are self-contained in their directories.
  This file coordinates the root-level build targets.
-/

-- Import active paper modules
import Papers.P2_BidualGap.P2_Minimal
-- P4, P5, P6 etc. are self-contained bundles; build from their directories

namespace Papers

/-! ### Papers Coordination -/

-- Each paper bundle builds independently via `lake build` from its directory
