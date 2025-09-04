/-
  Paper 4 Smoke target: builds S0–S4 wiring + certificates with no sorries.
  CI can call: lake build Papers.P4_SpectralGeometry.Smoke
-/
import Papers.P4_SpectralGeometry.Spectral.Basic
import Papers.P4_SpectralGeometry.Spectral.CompactApprox
import Papers.P4_SpectralGeometry.Spectral.MarkovSpectrum
import Papers.P4_SpectralGeometry.Spectral.LocaleSpatiality
import Papers.P4_SpectralGeometry.Spectral.WLPOPortal
import Papers.P4_SpectralGeometry.Spectral.QHO
import Papers.P4_SpectralGeometry.Spectral.Profiles
import Papers.P4_SpectralGeometry.Spectral.Certificates
import Papers.P4_SpectralGeometry.Spectral.RouteFlags

namespace Papers.P4_SpectralGeometry

open Papers.P4_SpectralGeometry.Spectral

/-- A dummy foundation for example checks. -/
def F0 : Spectral.Foundation := { tag := "F0" }

-- Example checks that the skeleton works:
example : CompactSpectralApprox_W.Witness F0 := True.intro
example : QHO_W.Witness F0 := True.intro

-- Tokenized witnesses: require instances to use them.
example [HasMP F0] : SpecApproxEqSpec_W.Witness F0 := S1_upper (F := F0)
example [HasDCω F0] : LocaleSpatiality_W.Witness F0 := S2_upper (F := F0)
example [HasWLPO F0] : SeparationRoute_W.Witness F0 := S3_upper (F := F0)

-- Profiles mini-algebra sanity checks:
def pWLPO : Profile := Profile.WLPO_only
def pFT   : Profile := Profile.FT_only
def pMix  : Profile := Profile.max pWLPO pFT

/-- The smoke target returns `True` to anchor a definition. -/
def ok : True := True.intro

end Papers.P4_SpectralGeometry