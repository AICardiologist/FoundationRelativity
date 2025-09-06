/-
  S4: Quantum Harmonic Oscillator (pinned exemplar) — height 0.
  Modeled as a universal (True) witness family.
-/
import Papers.P4_SpectralGeometry.Spectral.Basic

namespace Papers.P4_SpectralGeometry.Spectral

/-- S4 witness: holds for every foundation (height 0). -/
def QHO_W : WitnessFamily :=
  WitnessFamily.height0

/-- Smoke: S4 holds for every foundation (no sorries). -/
theorem qho_height0 (F : Foundation) :
    QHO_W.Witness F := trivial

end Papers.P4_SpectralGeometry.Spectral