/-
Copyright (c) 2025 Paul Chun-Kit Lee. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Paul Chun-Kit Lee
-/

import Papers.P4_SpectralGeometry.Spectral.Basic
import Papers.P4_SpectralGeometry.Spectral.Profiles
import Papers.P4_SpectralGeometry.Spectral.Certificates
import Papers.P4_SpectralGeometry.Spectral.LocaleSpatiality
import Papers.P4_SpectralGeometry.Spectral.WLPOPortal
import Papers.P4_SpectralGeometry.Spectral.CompactApprox
import Papers.P4_SpectralGeometry.Spectral.QHO

/-!
# Paper 4: Quantum Spectra — Profile-based upper bounds

Turn a 3-axis Profile (WLPO, FT, DCω) into token requirements,
then certify witness families from such "profile requirements".
We also prove the product/composition law: `and` ↔ componentwise `max`.
-/

namespace Papers.P4_SpectralGeometry.Spectral

open Height Profile WitnessFamily

/-- Tokens available at a foundation, restricted to the 3 primary axes. -/
structure TokenPack (F : Foundation) where
  WLPO : Prop := HasWLPO F
  FT   : Prop := HasFT F
  DCω  : Prop := HasDCω F

/-- Default pack: use the Paper-4 token classes. -/
def defaultPack (F : Foundation) : TokenPack F := {}

/-- Given a height and a token, produce the requirement prop for that axis. -/
def need (h : Height) (tok : Prop) : Prop :=
  match h with
  | Height.h0 => True
  | Height.h1 => tok
  | Height.hω => False    -- ω placeholder: no automatic discharge in this layer

/-- Requirements induced by a 3-axis profile at a given token pack. -/
def Requires {F : Foundation} (p : Profile) (P : TokenPack F) : Prop :=
  need p.hWLPO P.WLPO ∧ need p.hFT P.FT ∧ need p.hDCω P.DCω

/-- Basic `need` simplifications. -/
@[simp] theorem need_h0 (T : Prop) : need Height.h0 T = True := rfl
@[simp] theorem need_h1 (T : Prop) : need Height.h1 T = T := rfl
@[simp] theorem need_hω (T : Prop) : need Height.hω T = False := rfl

/-- Axiswise: `need (max a b)` equals `need a ∧ need b` (for {0,1,ω}). -/
theorem need_max (a b : Height) (T : Prop) :
  need (Height.max a b) T ↔ (need a T ∧ need b T) := by
  cases a <;> cases b <;> simp [Height.max, need, and_comm]
  -- The h1/h1 case reduces to `T ↔ (T ∧ T)`, which simp closes.

/-- Componentwise: requirements for max-profile are the conjunction of reqs. -/
theorem requires_max {F : Foundation} (p q : Profile) (P : TokenPack F) :
  Requires (Profile.max p q) P ↔ (Requires p P ∧ Requires q P) := by
  cases p; cases q; cases P
  simp [Requires, Profile.max, need_max, and_assoc, and_left_comm]

@[simp] theorem requires_all_zero_iff {F : Foundation} (P : TokenPack F) :
  Requires Profile.all_zero P ↔ True := by
  cases P; simp [Requires, Profile.all_zero, need]

@[simp] theorem requires_all_zero_default_iff (F : Foundation) :
  Requires Profile.all_zero (defaultPack F) ↔ True := by
  simp

/-- A profile-based upper bound certificate. -/
structure ProfileUpper (p : Profile) (W : WitnessFamily) : Prop where
  prove : ∀ F, Requires p (defaultPack F) → W.Witness F

/-- Composition: `(W₁ ∧ W₂)` holds under `max` of their profiles. -/
theorem ProfileUpper.and {p q : Profile} {W₁ W₂ : WitnessFamily}
    (h₁ : ProfileUpper p W₁) (h₂ : ProfileUpper q W₂) :
    ProfileUpper (Profile.max p q) (W₁.and W₂) :=
  ⟨fun F hReq =>
    match (requires_max p q (defaultPack F)).mp hReq with
    | ⟨hReq₁, hReq₂⟩ => And.intro (h₁.prove _ hReq₁) (h₂.prove _ hReq₂)⟩

/-! ### Canonical profile certificates for S0–S4 -/

/-- S0: compact/finite-rank ε-approximations — height 0 (`all_zero`). -/
def S0_profile : Profile := Profile.all_zero

def S0_ProfileUpper : ProfileUpper S0_profile CompactSpectralApprox_W :=
  ⟨fun _ _ => True.intro⟩

/-- S4: quantum harmonic oscillator — height 0 (`all_zero`). -/
def S4_profile : Profile := Profile.all_zero

def S4_ProfileUpper : ProfileUpper S4_profile QHO_W :=
  ⟨fun _ _ => True.intro⟩

/-- S3: route-conditional WLPO portal — `WLPO_only` profile. -/
def S3_profile : Profile := Profile.WLPO_only

@[simp] theorem requires_WLPO_only {F : Foundation} :
  Requires S3_profile (defaultPack F) ↔ HasWLPO F := by
  -- S3_profile = ⟨h1, h0, h0⟩ so requirements reduce to `HasWLPO F`.
  simp [S3_profile, Requires, defaultPack, need, Profile.WLPO_only]

def S3_ProfileUpper : ProfileUpper S3_profile SeparationRoute_W :=
  ⟨fun F hReq =>
    -- Locale witness is definitional `HasWLPO F` for S3:
    (requires_WLPO_only (F := F)).mp hReq⟩

/-- S2: locale spectrum spatiality (separable) — `DCω_only` profile (upper bound). -/
def S2_profile : Profile := Profile.DCω_only

@[simp] theorem requires_DCω_only {F : Foundation} :
  Requires S2_profile (defaultPack F) ↔ HasDCω F := by
  -- S2_profile = ⟨h0, h0, h1⟩ so requirements reduce to `HasDCω F`.
  simp [S2_profile, Requires, defaultPack, need, Profile.DCω_only]

def S2_ProfileUpper : ProfileUpper S2_profile LocaleSpatiality_W :=
  ⟨fun F hReq =>
    (requires_DCω_only (F := F)).mp hReq⟩

/-- A composed example: spatiality ∧ WLPO-portal carries `max DCω_only WLPO_only`. -/
def S2_S3_profile : Profile := Profile.max S2_profile S3_profile

def S2_S3_ProfileUpper :
    ProfileUpper S2_S3_profile (LocaleSpatiality_W.and SeparationRoute_W) :=
  (S2_ProfileUpper.and S3_ProfileUpper)

/-!
S1 (Specₐpprox = Spec) is calibrated by a separate axis (MP). We keep its
`IffToken HasMP` certificate in `Certificates.lean`, and record the WLPO/FT/DCω
coordinates here as height-0 (`all_zero`) to emphasize orthogonality.
-/
def S1_profile : Profile := Profile.all_zero

/-! ### FT axis demonstration (completeness) -/

/-- Demo witness for FT axis. -/
def FTPortal_W : WitnessFamily := WitnessFamily.fromToken (fun F => HasFT F)

@[simp] theorem requires_FT_only {F} :
  Requires Profile.FT_only (defaultPack F) ↔ HasFT F := by 
  simp [Profile.FT_only, Requires, need, defaultPack]

def S5_ProfileUpper : ProfileUpper Profile.FT_only FTPortal_W :=
  ⟨fun F h => (requires_FT_only (F := F)).mp h⟩

end Papers.P4_SpectralGeometry.Spectral