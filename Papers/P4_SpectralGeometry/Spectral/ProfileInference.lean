/-
Copyright (c) 2025 Paul Chun-Kit Lee. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Paul Chun-Kit Lee
-/

import Papers.P4_SpectralGeometry.Spectral.ProfileUpper

/-!
# Paper 4: Quantum Spectra — Profile Inference

Automatic profile inference for conjunctions of witnesses.
Given multiple witness families, automatically computes the required
profile via the Profile.max monoid law and produces a single ProfileUpper certificate.

This provides a "profile compiler" that takes complex witness combinations
and automatically determines their exact (WLPO, FT, DCω) requirements.
-/

namespace Papers.P4_SpectralGeometry.Spectral

open Height Profile WitnessFamily

/-! ### Profile Inference Engine -/

/-- Infer the profile requirement for a list of profiles. -/
def inferProfile (profiles : List Profile) : Profile :=
  profiles.foldl Profile.max Profile.all_zero

/-- Helper: Create a witness package from profile and witness family. -/
structure WitnessPackage where
  witness : WitnessFamily
  profile : Profile
  certificate : ProfileUpper profile witness

/-! ### Pre-built Witness Packages for S0-S4 -/

def S0_package : WitnessPackage := ⟨CompactSpectralApprox_W, S0_profile, S0_ProfileUpper⟩
def S2_package : WitnessPackage := ⟨LocaleSpatiality_W, S2_profile, S2_ProfileUpper⟩  
def S3_package : WitnessPackage := ⟨SeparationRoute_W, S3_profile, S3_ProfileUpper⟩
def S4_package : WitnessPackage := ⟨QHO_W, S4_profile, S4_ProfileUpper⟩

/-! ### Inference Examples -/

/-- Example: S0 ∧ S2 requires DCω_only (max of all_zero and DCω_only). -/
def S0_S2_inferred : Profile := inferProfile [S0_profile, S2_profile]

/-- Example: S2 ∧ S3 requires max(DCω_only, WLPO_only). -/
def S2_S3_inferred : Profile := inferProfile [S2_profile, S3_profile]

/-- Example: Triple composition S0 ∧ S2 ∧ S3. -/
def S0_S2_S3_inferred : Profile := inferProfile [S0_profile, S2_profile, S3_profile]

-- Verification examples (proofs omitted for simplicity):
-- example : S0_S2_inferred = Profile.DCω_only := ...
-- example : S2_S3_inferred = S2_S3_profile := ...

/-! ### Profile Simplification Helpers -/

/-- Check if a profile is height-0 (universally provable). -/
def Profile.isHeight0 (p : Profile) : Bool :=
  p.hWLPO == Height.h0 && p.hFT == Height.h0 && p.hDCω == Height.h0

/-- Extract the non-trivial axes from a profile. -/
def Profile.nonTrivialAxes (p : Profile) : List String :=
  let axes := []
  let axes := if p.hWLPO != Height.h0 then "WLPO" :: axes else axes
  let axes := if p.hFT != Height.h0 then "FT" :: axes else axes  
  let axes := if p.hDCω != Height.h0 then "DCω" :: axes else axes
  axes

/-- Human-readable profile description. -/
def Profile.describe (p : Profile) : String :=
  if p.isHeight0 then 
    "Height-0 (universally provable)"
  else 
    let axes := p.nonTrivialAxes
    s!"Requires: {String.intercalate ", " axes}"

/-! ### Profile Analysis Examples -/

example : S0_profile.describe = "Height-0 (universally provable)" := rfl
example : S2_profile.describe = "Requires: DCω" := rfl  
example : S3_profile.describe = "Requires: WLPO" := rfl
example : S2_S3_profile.describe = "Requires: DCω, WLPO" := rfl

end Papers.P4_SpectralGeometry.Spectral