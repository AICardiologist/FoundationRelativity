import Papers.P4_SpectralGeometry.Spectral.Basic
import Papers.P4_SpectralGeometry.Spectral.Profiles
import Papers.P4_SpectralGeometry.Spectral.Certificates
import Papers.P4_SpectralGeometry.Spectral.ProfileUpper
import Papers.P4_SpectralGeometry.Spectral.MarkovSpectrum

/-!
# Paper 4: Profiles with orthogonal MP bit
Adds a tiny MP switch that composes with boolean `||`, mirroring `Profile.max` on the 3 axes.
-/

namespace Papers.P4_SpectralGeometry.Spectral

/-- Bool‑gated requirement: if the bit is `true`, require `T`; else `True`. -/
@[simp] def needB : Bool → Prop → Prop
| true,  T => T
| false, _ => True

@[simp] theorem needB_true  (T : Prop) : needB true  T = T     := rfl
@[simp] theorem needB_false (T : Prop) : needB false T = True  := rfl

@[simp] theorem needB_or (b c : Bool) (T : Prop) :
  needB (b || c) T ↔ (needB b T ∧ needB c T) := by
  cases b <;> cases c <;> simp [needB, Bool.or]

/-- Extended profile: 3‑axis core plus an orthogonal MP bit. -/
structure ProfileX where
  core : Profile
  mp   : Bool
deriving Repr

namespace ProfileX
/-- Componentwise composition: `core` via `Profile.max`, MP via boolean `||`. -/
def max (p q : ProfileX) : ProfileX :=
  { core := Profile.max p.core q.core
  , mp   := p.mp || q.mp }

@[simp] theorem max_core (p q : ProfileX) :
  (max p q).core = Profile.max p.core q.core := rfl
@[simp] theorem max_mp (p q : ProfileX) :
  (max p q).mp = (p.mp || q.mp) := rfl

def all_zero : ProfileX := { core := Profile.all_zero, mp := false }
def MP_only  : ProfileX := { core := Profile.all_zero, mp := true  }
end ProfileX

/-- Requirements for the extended profile at a foundation `F`. -/
def RequiresX (F : Foundation) (px : ProfileX) : Prop :=
  Requires px.core (defaultPack F) ∧ needB px.mp (HasMP F)

@[simp] theorem RequiresX_mp_false (F : Foundation) (p : Profile) :
  RequiresX F ⟨p, false⟩ ↔ Requires p (defaultPack F) := by
  simp [RequiresX, needB]

@[simp] theorem RequiresX_mp_true (F : Foundation) (p : Profile) :
  RequiresX F ⟨p, true⟩ ↔ (Requires p (defaultPack F) ∧ HasMP F) := by
  simp [RequiresX, needB]

@[simp] theorem requiresX_max (F : Foundation) (p q : ProfileX) :
  RequiresX F (ProfileX.max p q) ↔ (RequiresX F p ∧ RequiresX F q) := by
  cases p with
  | mk pc pm =>
    cases q with
    | mk qc qm =>
      cases pm <;> cases qm <;> simp [RequiresX, ProfileX.max, requires_max, needB, and_left_comm, and_assoc, and_comm]

/-- Extended certificate: profile+MP guard. -/
structure ProfileUpperX (px : ProfileX) (W : WitnessFamily) : Prop where
  prove : ∀ F, RequiresX F px → W.Witness F

/-- Composition law mirrors `ProfileUpper.and`. -/
theorem ProfileUpperX.and {p q : ProfileX} {W₁ W₂ : WitnessFamily}
  (h₁ : ProfileUpperX p W₁) (h₂ : ProfileUpperX q W₂) :
  ProfileUpperX (ProfileX.max p q) (W₁.and W₂) :=
⟨fun F h =>
  match (requiresX_max F p q).mp h with
  | ⟨hp, hq⟩ => And.intro (h₁.prove F hp) (h₂.prove F hq)⟩

/-- Lift a pure 3‑axis certificate into the extended system (mp=false). -/
def liftX {p : Profile} {W : WitnessFamily} (h : ProfileUpper p W) :
  ProfileUpperX ⟨p,false⟩ W :=
⟨fun F hReq => h.prove F hReq.left⟩

/-- S0–S4 in the extended system (mp=false). -/
def S0_ProfileUpperX : ProfileUpperX ⟨S0_profile, false⟩ CompactSpectralApprox_W := liftX S0_ProfileUpper
def S2_ProfileUpperX : ProfileUpperX ⟨S2_profile, false⟩ LocaleSpatiality_W     := liftX S2_ProfileUpper
def S3_ProfileUpperX : ProfileUpperX ⟨S3_profile, false⟩ SeparationRoute_W     := liftX S3_ProfileUpper
def S4_ProfileUpperX : ProfileUpperX ⟨S4_profile, false⟩ QHO_W                  := liftX S4_ProfileUpper

/-- S1 in the extended system (mp=true), reusing `S1_iff_MP`. -/
def S1_ProfileUpperX : ProfileUpperX ⟨S1_profile, true⟩ SpecApproxEqSpec_W :=
⟨fun F h =>
  -- `h.right : needB true (HasMP F)` reduces to `HasMP F`.
  have hMP : HasMP F := by simpa [RequiresX, needB] using h.right
  (S1_iff_MP.mp F) hMP⟩

/-- Example: (S1 ∧ S2) composes to `max ⟨S1, true⟩ ⟨S2, false⟩`. -/
def S1_S2_ProfileUpperX :
  ProfileUpperX (ProfileX.max ⟨S1_profile, true⟩ ⟨S2_profile, false⟩)
                (SpecApproxEqSpec_W.and LocaleSpatiality_W) :=
  (S1_ProfileUpperX.and S2_ProfileUpperX)

end Papers.P4_SpectralGeometry.Spectral