/-
Copyright (c) 2025 Paul Chun-Kit Lee. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Paul Chun-Kit Lee
-/

import Papers.P4_SpectralGeometry.Spectral.Basic
import Papers.P4_SpectralGeometry.Spectral.WLPOPortal
import Papers.P4_SpectralGeometry.Spectral.Certificates

/-!
# Paper 4: Quantum Spectra — Route Flags

Lightweight flags to tag proof routes. This is intentionally schematic,
but provides a place to hang "portal" implications.
-/

namespace Papers.P4_SpectralGeometry.Spectral

/-- Flag: a route that applies separation in a non-separable context. -/
def UsesSeparationNonSep (F : Foundation) : Prop := True

/-- Portal lemma shape: using that route demands WLPO to discharge the witness. -/
def PortalRequiresWLPO :
  UpperBound (fun F => HasWLPO F ∧ UsesSeparationNonSep F) SeparationRoute_W :=
by
  refine ⟨?_⟩
  intro F h
  -- SeparationRoute_W is `fromToken HasWLPO`, so its witness at F is `HasWLPO F`.
  -- From h : HasWLPO F ∧ UsesSeparationNonSep F, take left component.
  exact h.left

end Papers.P4_SpectralGeometry.Spectral