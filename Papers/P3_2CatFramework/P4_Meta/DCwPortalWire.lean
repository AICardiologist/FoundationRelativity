/-
  File: Papers/P3_2CatFramework/P4_Meta/DCwPortalWire.lean

  Purpose:
  - Wire the DCω axis calibrator through the Frontier infrastructure
  - Instantiate the Baire token and the DCω ⇒ Baire reduction (as an axiom with paper citation)
  - Provide a small height-lifting helper
-/
import Papers.P3_2CatFramework.P4_Meta.DCw_Frontier
import Papers.P3_2CatFramework.P4_Meta.IndependenceRegistry

namespace Papers.P4Meta

section DCwPortalWire

-- Tokens (DCw already declared in IndependenceRegistry)
open Papers.P4Meta
axiom Baire : Prop

/-- DCω ⇒ Baire (paper-cited axiom; Lean uses it as a one-line reduction). -/
axiom DCw_to_Baire : DCw → Baire

/-- Height-lift helper: given a height certificate for DCω, produce one for Baire. -/
@[inline] def Baire_height1_from_DCw
  {HeightCert : Prop → Prop}
  (height_mono : ∀ {P Q}, (P → Q) → HeightCert P → HeightCert Q)
  (dcw_h1 : HeightCert DCw) : HeightCert Baire :=
  (Papers.P4Meta.Baire_height1
    (DCw := DCw) (Baire := Baire) (DCw_to_Baire := DCw_to_Baire)
    (HeightCert := HeightCert) height_mono) dcw_h1

end DCwPortalWire

end Papers.P4Meta