/-
  S0: Compact spectral approximation (height 0 core).
  We model it as a witness family that is True for all foundations.
-/
import Papers.P4_SpectralGeometry.Spectral.Basic

namespace Papers.P4_SpectralGeometry.Spectral

/-- S0 witness: exists for every foundation (height 0). -/
def CompactSpectralApprox_W : WitnessFamily :=
  WitnessFamily.height0

/-- Smoke: S0 holds for every foundation (no sorries). -/
theorem compact_height0 (F : Foundation) :
    CompactSpectralApprox_W.Witness F := trivial

end Papers.P4_SpectralGeometry.Spectral