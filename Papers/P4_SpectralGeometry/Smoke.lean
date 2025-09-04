/-
  Paper 4 Smoke target: builds S0–S4 wiring with no sorries.
  CI can call: lake build Papers.P4_SpectralGeometry.Smoke
-/
import Papers.P4_SpectralGeometry.Spectral.Basic
import Papers.P4_SpectralGeometry.Spectral.CompactApprox
import Papers.P4_SpectralGeometry.Spectral.MarkovSpectrum
import Papers.P4_SpectralGeometry.Spectral.LocaleSpatiality
import Papers.P4_SpectralGeometry.Spectral.WLPOPortal
import Papers.P4_SpectralGeometry.Spectral.QHO

namespace Papers.P4_SpectralGeometry

open Spectral

/-- All Paper-4 witnesses hold under the expected tokens (upper bounds). -/
theorem Smoke :
    (∀ F, CompactSpectralApprox_W.Witness F) ∧
    (∀ F, QHO_W.Witness F) ∧
    (∀ F, (HasMP F) → SpecApproxEqSpec_W.Witness F) ∧
    (∀ F, (HasDCω F) → LocaleSpatiality_W.Witness F) ∧
    (∀ F, (HasWLPO F) → SeparationRoute_W.Witness F) := by
  refine ⟨
    (fun F => compact_height0 F),
    (fun F => qho_height0 F),
    (fun F h => by
      have _inst : HasMP F := h
      exact spec_upper),
    (fun F h => by
      have _inst : HasDCω F := h
      exact locale_upper),
    (fun F h => by
      have _inst : HasWLPO F := h
      exact separation_portal)
  ⟩

end Papers.P4_SpectralGeometry