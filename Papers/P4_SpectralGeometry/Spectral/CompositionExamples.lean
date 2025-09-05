/-
Copyright (c) 2025 Paul Chun-Kit Lee. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Paul Chun-Kit Lee
-/

import Papers.P4_SpectralGeometry.Spectral.ProfileUpper
import Papers.P4_SpectralGeometry.Spectral.MarkovSpectrum

/-!
# Paper 4: Quantum Spectra — Composition Examples

Comprehensive examples demonstrating profile composition laws and witness combinations.
Shows how different spectral claims compose under the AxCal framework with concrete
profile calculations and upper bound certificates.
-/

namespace Papers.P4_SpectralGeometry.Spectral

open Height Profile WitnessFamily

/-! ### Binary Compositions -/

/-- S0 ∧ S2: Compact approximation with locale spatiality. -/
def S0_S2_profile : Profile := Profile.max S0_profile S2_profile

def S0_S2_ProfileUpper : ProfileUpper S0_S2_profile (CompactSpectralApprox_W.and LocaleSpatiality_W) :=
  S0_ProfileUpper.and S2_ProfileUpper

/-- S0 ∧ S3: Compact approximation with WLPO portal. -/
def S0_S3_profile : Profile := Profile.max S0_profile S3_profile

def S0_S3_ProfileUpper : ProfileUpper S0_S3_profile (CompactSpectralApprox_W.and SeparationRoute_W) :=
  S0_ProfileUpper.and S3_ProfileUpper

/-- S0 ∧ S4: Both compact claims together (both height-0). -/
def S0_S4_profile : Profile := Profile.max S0_profile S4_profile  

def S0_S4_ProfileUpper : ProfileUpper S0_S4_profile (CompactSpectralApprox_W.and QHO_W) :=
  S0_ProfileUpper.and S4_ProfileUpper

/-- S1 ∧ S2: Markov spectrum with locale spatiality (orthogonal axes). -/
def S1_S2_profile : Profile := Profile.max S1_profile S2_profile

-- Note: S1_S2 would need both MP and DCω tokens since they're on orthogonal axes
-- This demonstrates how orthogonal axes accumulate independently

/-- S2 ∧ S4: Locale spatiality with QHO (DCω requirement dominates). -/
def S2_S4_profile : Profile := Profile.max S2_profile S4_profile

def S2_S4_ProfileUpper : ProfileUpper S2_S4_profile (LocaleSpatiality_W.and QHO_W) :=
  S2_ProfileUpper.and S4_ProfileUpper

/-- S3 ∧ S4: WLPO portal with QHO (WLPO requirement dominates). -/
def S3_S4_profile : Profile := Profile.max S3_profile S4_profile

def S3_S4_ProfileUpper : ProfileUpper S3_S4_profile (SeparationRoute_W.and QHO_W) :=
  S3_ProfileUpper.and S4_ProfileUpper

/-! ### Triple Compositions -/

/-- S0 ∧ S2 ∧ S3: All major components except QHO. -/
def S0_S2_S3_profile : Profile := Profile.max (Profile.max S0_profile S2_profile) S3_profile

def S0_S2_S3_ProfileUpper : 
    ProfileUpper S0_S2_S3_profile 
                 ((CompactSpectralApprox_W.and LocaleSpatiality_W).and SeparationRoute_W) :=
  (S0_ProfileUpper.and S2_ProfileUpper).and S3_ProfileUpper

/-- S0 ∧ S2 ∧ S4: Compact claims with locale spatiality. -/
def S0_S2_S4_profile : Profile := Profile.max (Profile.max S0_profile S2_profile) S4_profile

def S0_S2_S4_ProfileUpper :
    ProfileUpper S0_S2_S4_profile
                 ((CompactSpectralApprox_W.and LocaleSpatiality_W).and QHO_W) :=
  (S0_ProfileUpper.and S2_ProfileUpper).and S4_ProfileUpper

/-- S0 ∧ S3 ∧ S4: Compact claims with WLPO portal. -/  
def S0_S3_S4_profile : Profile := Profile.max (Profile.max S0_profile S3_profile) S4_profile

def S0_S3_S4_ProfileUpper :
    ProfileUpper S0_S3_S4_profile
                 ((CompactSpectralApprox_W.and SeparationRoute_W).and QHO_W) :=
  (S0_ProfileUpper.and S3_ProfileUpper).and S4_ProfileUpper

/-- S2 ∧ S3 ∧ S4: All non-compact claims together. -/
def S2_S3_S4_profile : Profile := Profile.max (Profile.max S2_profile S3_profile) S4_profile

def S2_S3_S4_ProfileUpper :
    ProfileUpper S2_S3_S4_profile
                 ((LocaleSpatiality_W.and SeparationRoute_W).and QHO_W) :=
  (S2_ProfileUpper.and S3_ProfileUpper).and S4_ProfileUpper

/-! ### Full Composition -/

/-- All spectral claims S0 ∧ S2 ∧ S3 ∧ S4 together. -/
def all_spectral_profile : Profile := 
  Profile.max (Profile.max (Profile.max S0_profile S2_profile) S3_profile) S4_profile

def all_spectral_ProfileUpper :
    ProfileUpper all_spectral_profile
                 (((CompactSpectralApprox_W.and LocaleSpatiality_W).and SeparationRoute_W).and QHO_W) :=
  ((S0_ProfileUpper.and S2_ProfileUpper).and S3_ProfileUpper).and S4_ProfileUpper

/-! ### Profile Analysis Lemmas -/

/-- S0 ∧ S2 requires exactly DCω (height-0 ∨ DCω = DCω). -/
theorem S0_S2_requires_DCω : S0_S2_profile = Profile.DCω_only := 
  rfl

/-- S0 ∧ S3 requires exactly WLPO (height-0 ∨ WLPO = WLPO). -/
theorem S0_S3_requires_WLPO : S0_S3_profile = Profile.WLPO_only := 
  rfl

/-- S0 ∧ S4 is height-0 (height-0 ∨ height-0 = height-0). -/
theorem S0_S4_is_height0 : S0_S4_profile = Profile.all_zero := 
  rfl

/-- S2 ∧ S3 requires both DCω and WLPO. -/
theorem S2_S3_requires_both : 
    S2_S3_profile = ⟨Height.h1, Height.h0, Height.h1⟩ := 
  rfl

/-! ### Practical Composition Shortcuts -/

/-- Helper: Compose two ProfileUpper certificates. -/
def compose2 {p1 p2 : Profile} {W1 W2 : WitnessFamily}
    (cert1 : ProfileUpper p1 W1) (cert2 : ProfileUpper p2 W2) :
    ProfileUpper (Profile.max p1 p2) (W1.and W2) :=
  cert1.and cert2

/-- Helper: Compose three ProfileUpper certificates. -/
def compose3 {p1 p2 p3 : Profile} {W1 W2 W3 : WitnessFamily}
    (cert1 : ProfileUpper p1 W1) (cert2 : ProfileUpper p2 W2) (cert3 : ProfileUpper p3 W3) :
    ProfileUpper (Profile.max (Profile.max p1 p2) p3) ((W1.and W2).and W3) :=
  (cert1.and cert2).and cert3

/-- Helper: Compose four ProfileUpper certificates. -/
def compose4 {p1 p2 p3 p4 : Profile} {W1 W2 W3 W4 : WitnessFamily}
    (cert1 : ProfileUpper p1 W1) (cert2 : ProfileUpper p2 W2) 
    (cert3 : ProfileUpper p3 W3) (cert4 : ProfileUpper p4 W4) :
    ProfileUpper (Profile.max (Profile.max (Profile.max p1 p2) p3) p4) 
                 (((W1.and W2).and W3).and W4) :=
  ((cert1.and cert2).and cert3).and cert4

/-! ### Verification Examples Using Shortcuts -/

/-- Alternative definition of all_spectral using compose4. -/
def all_spectral_alt : ProfileUpper all_spectral_profile 
    (((CompactSpectralApprox_W.and LocaleSpatiality_W).and SeparationRoute_W).and QHO_W) :=
  compose4 S0_ProfileUpper S2_ProfileUpper S3_ProfileUpper S4_ProfileUpper

/-- The two definitions are definitionally equal. -/
example : all_spectral_ProfileUpper = all_spectral_alt := rfl

end Papers.P4_SpectralGeometry.Spectral