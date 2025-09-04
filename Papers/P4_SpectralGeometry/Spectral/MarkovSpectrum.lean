/-
  S1: Spec_approx = Spec (upper direction under MP).
  We encode the upper bound by making the witness exactly `HasMP F`.
-/
import Papers.P4_SpectralGeometry.Spectral.Basic

namespace Papers.P4_SpectralGeometry.Spectral

/-- S1 witness holds exactly when the MP token is available. -/
def SpecApproxEqSpec_W : WitnessFamily :=
  WitnessFamily.fromToken (fun F => HasMP F)

/-- Smoke: with `[HasMP F]`, the S1 witness holds. -/
theorem spec_upper {F : Foundation} [h : HasMP F] :
    SpecApproxEqSpec_W.Witness F := h

end Papers.P4_SpectralGeometry.Spectral