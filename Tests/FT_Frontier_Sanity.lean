/-
  File: Tests/FT_Frontier_Sanity.lean
  
  Purpose:
  - Micro-tests for the FT frontier infrastructure
  - Verify reduction composition and height lifting work correctly
  - No heavy dependencies, just API protection during refactors
-/
import Papers.P3_2CatFramework.P4_Meta.FT_Frontier
import Papers.P3_2CatFramework.P4_Meta.FTPortalWire

open Papers.P4Meta

section BasicReductions
  variable {FT UCT Sperner BFPT : Prop}
  variable (ft_to_uct : FT → UCT)
  variable (ft_to_sperner : FT → Sperner)
  variable (sperner_to_bfpt : Sperner → BFPT)

  -- Test that reductions compose properly
  example : ReducesTo FT BFPT :=
    (reduces ft_to_sperner).trans (reduces sperner_to_bfpt)

  -- Test calc chains work
  example : ReducesTo FT BFPT := by
    calc ReducesTo FT Sperner := reduces ft_to_sperner
         ReducesTo _ BFPT     := reduces sperner_to_bfpt

  -- Test direct composition
  example (ft : FT) : BFPT :=
    sperner_to_bfpt (ft_to_sperner ft)
end BasicReductions

section HeightLifting
  variable {HeightCert : Prop → Prop}
  variable {FT UCT Sperner BFPT : Prop}
  variable (height_mono : ∀ {P Q}, (P → Q) → HeightCert P → HeightCert Q)
  variable (ft_h1 : HeightCert FT)
  variable (ft_to_uct : FT → UCT)
  variable (ft_to_sperner : FT → Sperner)
  variable (sperner_to_bfpt : Sperner → BFPT)

  -- Test height lifting for UCT
  example : HeightCert UCT :=
    height_lift_of_imp height_mono ft_h1 ft_to_uct

  -- Test height lifting for BFPT via composition
  example : HeightCert BFPT :=
    let ft_to_bfpt := fun ft => sperner_to_bfpt (ft_to_sperner ft)
    height_lift_of_imp height_mono ft_h1 ft_to_bfpt

  -- Test using the wired versions
  example : HeightCert UCT :=
    UCT_height1_from_FT height_mono ft_h1 ft_to_uct

  example : HeightCert BFPT :=
    BFPT_height1_from_FT height_mono ft_h1 ft_to_sperner sperner_to_bfpt
end HeightLifting

section OrthogonalAxes
  variable {WLPO Gap FT UCT : Prop}
  variable (portal : Gap ↔ WLPO)
  variable (ft_to_uct : FT → UCT)
  
  -- UCT can be reached from FT (height 1 on FT axis)
  -- UCT doesn't need WLPO (height 0 on WLPO axis)
  -- These are orthogonal paths to UCT
  
  variable (wlpo_not_needed_for_uct : UCT)  -- UCT holds without WLPO
  variable (ft_proves_uct : FT → UCT)       -- FT proves UCT
  
  -- This captures the independence: UCT sits at different heights on different axes
end OrthogonalAxes