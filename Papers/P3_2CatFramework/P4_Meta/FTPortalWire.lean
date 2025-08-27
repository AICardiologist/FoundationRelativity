/-
  File: Papers/P3_2CatFramework/P4_Meta/FTPortalWire.lean
  
  Purpose:
  - Wire the FT axis calibrators through the Frontier infrastructure
  - Instantiate tokens with actual calibrator definitions
  - Provide height certificates at specific levels
-/
import Papers.P3_2CatFramework.P4_Meta.FT_Frontier

namespace Papers.P4Meta

section FTAxisCalibrators

-- Abstract propositions for the Fan Theorem axis
variable {FT UCT Sperner BFPT : Prop}

/-- UCT at height 1 from FT, height 0 from WLPO. -/
def UCT_height1_from_FT {HeightCert : Prop → Prop}
    (height_mono : ∀ {P Q}, (P → Q) → HeightCert P → HeightCert Q)
    (ft_h1 : HeightCert FT) 
    (ft_to_uct : FT → UCT) : HeightCert UCT :=
  height_lift_of_imp height_mono ft_h1 ft_to_uct

/-- BFPT at height 1 from FT, height 0 from WLPO. -/
def BFPT_height1_from_FT {HeightCert : Prop → Prop}
    (height_mono : ∀ {P Q}, (P → Q) → HeightCert P → HeightCert Q)
    (ft_h1 : HeightCert FT)
    (ft_to_sperner : FT → Sperner)
    (sperner_to_bfpt : Sperner → BFPT) : HeightCert BFPT :=
  let ft_to_bfpt := fun ft => sperner_to_bfpt (ft_to_sperner ft)
  height_lift_of_imp height_mono ft_h1 ft_to_bfpt

/-- Sperner at height 1 from FT. -/
def Sperner_height1_from_FT {HeightCert : Prop → Prop}
    (height_mono : ∀ {P Q}, (P → Q) → HeightCert P → HeightCert Q)
    (ft_h1 : HeightCert FT)
    (ft_to_sperner : FT → Sperner) : HeightCert Sperner :=
  height_lift_of_imp height_mono ft_h1 ft_to_sperner

/-! ### Height table entries

For documentation purposes, we record the height assignments:
- h_{FT}(UCT) = 1 (proven via FT ⇒ UCT)
- h_{WLPO}(UCT) = 0 (UCT doesn't need WLPO)
- h_{FT}(BFPT_n) = 1 (proven via FT ⇒ Sperner ⇒ BFPT)
- h_{WLPO}(BFPT_n) = 0 (BFPT doesn't need WLPO)
- h_{FT}(Sperner) = 1 (proven via FT ⇒ Sperner)

Lower bounds remain as paper citations to models where BISH + ¬FT
fails UCT, Sperner, or BFPT.
-/

end FTAxisCalibrators

/-! ### Example usage pattern

This shows how to use the FT axis machinery once the proof terms
are available. The actual proofs of FT ⇒ UCT etc. will be added
when implementing the mechanizable versions.
-/
section UsageExample
  variable (FT UCT Sperner BFPT : Prop)
  variable (ft_to_uct : FT → UCT)
  variable (ft_to_sperner : FT → Sperner)
  variable (sperner_to_bfpt : Sperner → BFPT)
  
  -- Compose reductions
  example : FT → BFPT :=
    FT_to_BFPT (FT := FT) (Sperner := Sperner) (BFPT_n := BFPT)
      (FT_to_Sperner := ft_to_sperner) (Sperner_to_BFPT := sperner_to_bfpt)
  
  -- Use calc chains
  example : FT ⟶ BFPT := by
    calc FT ⟶ Sperner := reduces ft_to_sperner
         _  ⟶ BFPT    := reduces sperner_to_bfpt
end UsageExample

end Papers.P4Meta