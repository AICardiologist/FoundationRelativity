/-
Copyright (c) 2025 Paul Chun-Kit Lee. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Paul Chun-Kit Lee
-/

import Papers.P4_SpectralGeometry.Spectral.Basic
import Papers.P4_SpectralGeometry.Spectral.CompactApprox
import Papers.P4_SpectralGeometry.Spectral.MarkovSpectrum
import Papers.P4_SpectralGeometry.Spectral.LocaleSpatiality
import Papers.P4_SpectralGeometry.Spectral.WLPOPortal
import Papers.P4_SpectralGeometry.Spectral.QHO

/-!
# Paper 4: Quantum Spectra — Certificates

Upper-bound and equivalence certificates for witness families,
plus compositional laws. This lets us state "Height 0", "Iff Token",
and product-style upper bounds in Lean without mathlib.
-/

namespace Papers.P4_SpectralGeometry.Spectral

/-- Upper bound: Token ⇒ Witness, uniformly in the foundation. -/
structure UpperBound (Token : Foundation → Prop) (W : WitnessFamily) : Prop where
  run : ∀ F, Token F → W.Witness F

/-- Exact equivalence: Witness holds iff Token holds, foundationwise. -/
structure IffToken (Token : Foundation → Prop) (W : WitnessFamily) : Prop where
  mp  : ∀ F, Token F → W.Witness F
  mpr : ∀ F, W.Witness F → Token F

namespace WitnessFamily

/-- Combine two witness families by conjunction. -/
def and (W₁ W₂ : WitnessFamily) : WitnessFamily :=
  ⟨fun F => W₁.Witness F ∧ W₂.Witness F⟩

@[simp] theorem and_witness (W₁ W₂ : WitnessFamily) (F : Foundation) :
  (W₁.and W₂).Witness F ↔ (W₁.Witness F ∧ W₂.Witness F) := Iff.rfl

/-- `fromToken` is definitionally iff its token. -/
@[simp] theorem fromToken_iff (Token : Foundation → Prop) (F : Foundation) :
  (fromToken Token).Witness F ↔ Token F := Iff.rfl

/-- `fromToken` gives an upper bound trivially. -/
theorem fromToken_upper (Token : Foundation → Prop) :
  UpperBound Token (fromToken Token) :=
  ⟨fun _ h => h⟩

/-- `fromToken` gives a full iff certificate. -/
theorem fromToken_iffToken (Token : Foundation → Prop) :
  IffToken Token (fromToken Token) :=
  { mp  := fun _ h => h
  , mpr := fun _ h => h }

end WitnessFamily

/-- Composition law: upper bounds distribute over `.and`. -/
theorem UpperBound.and {A B : Foundation → Prop}
    {W₁ W₂ : WitnessFamily}
    (h₁ : UpperBound A W₁) (h₂ : UpperBound B W₂) :
    UpperBound (fun F => A F ∧ B F) (W₁.and W₂) :=
  ⟨fun F hAB => And.intro (h₁.run F hAB.left) (h₂.run F hAB.right)⟩

/-- Height-0 certificate: witness holds in all foundations. -/
def Height0 (W : WitnessFamily) : Prop := ∀ F, W.Witness F

/-- Height-0 intro for `height0`. -/
theorem Height0_height0 : Height0 WitnessFamily.height0 :=
  fun _ => True.intro

/-- Concrete certificates for S0–S4 (paper statements). -/

-- S0: Compact/finite-rank ε-approximations — height 0.
def S0_height0 : Height0 CompactSpectralApprox_W :=
  fun _ => True.intro

-- S4: QHO pinned exemplar — height 0.
def S4_height0 : Height0 QHO_W :=
  fun _ => True.intro

-- S1: Spec_approx = Spec   ↔  MP.
def S1_iff_MP : IffToken (fun F => HasMP F) SpecApproxEqSpec_W :=
  WitnessFamily.fromToken_iffToken (fun F => HasMP F)

-- S2: Locale spectrum spatiality (separable): upper bound DCω (we model as iff for the token witness).
def S2_iff_DCω : IffToken (fun F => HasDCω F) LocaleSpatiality_W :=
  WitnessFamily.fromToken_iffToken (fun F => HasDCω F)

-- S3: Separation portal in non-separable context: upper bound WLPO (modeled as iff for the token witness).
def S3_iff_WLPO : IffToken (fun F => HasWLPO F) SeparationRoute_W :=
  WitnessFamily.fromToken_iffToken (fun F => HasWLPO F)

/-- Small smoke-style lemmas that can be used in docs/tests. -/
theorem S1_upper {F : Foundation} [h : HasMP F] :
    SpecApproxEqSpec_W.Witness F := h

theorem S2_upper {F : Foundation} [h : HasDCω F] :
    LocaleSpatiality_W.Witness F := h

theorem S3_upper {F : Foundation} [h : HasWLPO F] :
    SeparationRoute_W.Witness F := h

end Papers.P4_SpectralGeometry.Spectral