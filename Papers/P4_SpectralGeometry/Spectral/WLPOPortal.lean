/-
  S3: WLPO portal for separation-based routes in non-separable contexts.
  We encode the (route-conditional) frontier by tying the witness to `HasWLPO F`.
-/
import Papers.P4_SpectralGeometry.Spectral.Basic

namespace Papers.P4_SpectralGeometry.Spectral

/-- S3 witness holds exactly when the WLPO token is available. -/
def SeparationRoute_W : WitnessFamily :=
  WitnessFamily.fromToken (fun F => HasWLPO F)

/-- Smoke: with `[HasWLPO F]`, the S3 witness holds. -/
theorem separation_portal {F : Foundation} [h : HasWLPO F] :
    SeparationRoute_W.Witness F := h

end Papers.P4_SpectralGeometry.Spectral