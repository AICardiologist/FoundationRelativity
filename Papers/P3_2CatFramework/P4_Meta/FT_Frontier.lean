/-
  File: Papers/P3_2CatFramework/P4_Meta/FT_Frontier.lean
  Purpose:
  - Add an FT/WKL-style axis and wire analytic calibrators as Prop-level tokens
  - Provide one-line reductions (FT ⇒ UCT, FT ⇒ Sperner ⇒ BFPTₙ)
  - Lift height certificates along these implications
  This mirrors the WLPO/GAP portal style but needs no portal: we just use ⇒ and height_mono.
-/
import Papers.P3_2CatFramework.P4_Meta.Frontier_API

namespace Papers.P4Meta

section FTAxis

-- Axis token: Fan Theorem (constructive; classically ↔ WKL)
variable (FT : Prop)

-- Calibrator tokens (pinned objects are implicit in the token name)
-- UCT_01: Uniform continuity on [0,1]
variable (UCT_01 : Prop)
-- Sperner: Sperner's lemma (finite triangulations)
variable (Sperner : Prop)
-- BFPT_n: Brouwer fixed-point theorem (for fixed n≥2)
variable (BFPT_n : Prop)

/-! ### Reductions (upper bounds) -/

-- FT ⇒ UCT on [0,1] (constructive folklore; mechanizable via moduli)
variable (FT_to_UCT : FT → UCT_01)

-- FT ⇒ Sperner (compactness/finite-branching strength)
variable (FT_to_Sperner : FT → Sperner)

-- Sperner ⇒ BFPTₙ (standard triangulation)
variable (Sperner_to_BFPT : Sperner → BFPT_n)

/-- Compose FT ⇒ BFPTₙ. -/
@[inline] def FT_to_BFPT : FT → BFPT_n :=
  fun ft => Sperner_to_BFPT (FT_to_Sperner ft)

/-! ### Ergonomic wrappers via your reductions API -/

@[inline] def FT_to_UCT_red : ReducesTo FT UCT_01 :=
  reduces FT_to_UCT

@[inline] def FT_to_Sperner_red : ReducesTo FT Sperner :=
  reduces FT_to_Sperner

@[inline] def Sperner_to_BFPT_red : ReducesTo Sperner BFPT_n :=
  reduces Sperner_to_BFPT

/-- FT ⟶ BFPTₙ as a composed reduction. -/
@[inline] def FT_to_BFPT_red : ReducesTo FT BFPT_n :=
  reduces (fun ft => Sperner_to_BFPT (FT_to_Sperner ft))

/-! ### Height transport (upper bounds as certificates)

We stay generic: `HeightCert : Prop → Prop` and `height_mono : (P → Q) → HeightCert P → HeightCert Q`.
-/
section Height
  variable {HeightCert : Prop → Prop}
  variable (height_mono : ∀ {P Q}, (P → Q) → HeightCert P → HeightCert Q)

  /-- If FT is height‑1 on the FT axis, then UCT is height‑1. -/
  @[inline] def UCT_height1
      (ft_h1 : HeightCert FT) : HeightCert UCT_01 :=
    height_lift_of_imp height_mono ft_h1 FT_to_UCT

  /-- If FT is height‑1, then BFPTₙ is height‑1. -/
  @[inline] def BFPT_height1
      (ft_h1 : HeightCert FT) : HeightCert BFPT_n :=
    let composed := fun ft => Sperner_to_BFPT (FT_to_Sperner ft)
    height_lift_of_imp height_mono ft_h1 composed
end Height

/-! ### Sanity: `calc` chains with ReducesTo notation -/
section Sanity
  example : ReducesTo FT BFPT_n :=
    reduces (fun ft => Sperner_to_BFPT (FT_to_Sperner ft))
end Sanity

end FTAxis

end Papers.P4Meta