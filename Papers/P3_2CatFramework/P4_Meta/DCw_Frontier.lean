/-
  File: Papers/P3_2CatFramework/P4_Meta/DCw_Frontier.lean

  Purpose:
  - Add a DCω axis and wire the Baire calibrator as a Prop-level token
  - Provide one-line reduction (DCω ⇒ Baire)
  - Lift height certificates along the implication
  This mirrors FT_Frontier.lean and uses the same Frontier_API.
-/
import Papers.P3_2CatFramework.P4_Meta.Frontier_API

namespace Papers.P4Meta

section DCAxis

variable (DCw : Prop)  -- Axis token: countable dependent choice (DCω)
variable (Baire : Prop)  -- Calibrator token: "pinned complete separable metric space is Baire"
variable (DCw_to_Baire : DCw → Baire)  -- DCω ⇒ Baire (standard argument: build the dense Gδ via dependent choices)

/-! ### Ergonomic wrapper via your reductions API -/

/-- A `ReducesTo` wrapper for DCω ⇒ Baire. -/
@[inline] def DCw_to_Baire_red : ReducesTo DCw Baire :=
  reduces DCw_to_Baire

/-! ### Height transport (upper bounds as certificates) -/

section Height
  variable {HeightCert : Prop → Prop}
  variable (height_mono : ∀ {P Q}, (P → Q) → HeightCert P → HeightCert Q)

/-- If DCω is height‑1 on the DCω axis, then the Baire calibrator is height‑1. -/
@[inline] def Baire_height1 (dcw_h1 : HeightCert DCw) : HeightCert Baire :=
  height_lift_of_imp height_mono dcw_h1 DCw_to_Baire
end Height

/-! ### Sanity -/
section Sanity
  -- Just shows the DCω ⟶ Baire reduction is packaged correctly
  example : DCw_to_Baire_red (DCw := DCw) (Baire := Baire) (DCw_to_Baire := DCw_to_Baire) =
           reduces DCw_to_Baire := rfl
end Sanity

end DCAxis

end Papers.P4Meta