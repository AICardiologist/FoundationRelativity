/-
  S2: Locale spectral spatiality (separable case) — upper bound via DCω.
  We encode the upper bound by making the witness exactly `HasDCω F`.
-/
import Papers.P4_SpectralGeometry.Spectral.Basic

namespace Papers.P4_SpectralGeometry.Spectral

/-- S2 witness holds exactly when the DCω token is available. -/
def LocaleSpatiality_W : WitnessFamily :=
  WitnessFamily.fromToken (fun F => HasDCω F)

/-- Smoke: with `[HasDCω F]`, the S2 witness holds. -/
theorem locale_upper {F : Foundation} [h : HasDCω F] :
    LocaleSpatiality_W.Witness F := h

end Papers.P4_SpectralGeometry.Spectral