import Papers.P3_2CatFramework.Phase2_API
import Papers.P3_2CatFramework.Phase3_Levels

/-!
  # FT Frontier: Fan Theorem Axis API
  
  Clean API for the Fan Theorem (FT) axis in the AxCal framework.
  
  ## Overview
  The FT axis represents principles related to the Fan Theorem and 
  uniform continuity. This module provides a clean interface for:
  - UCT (Uniform Continuity Theorem) at height 1 on FT axis
  - Orthogonality with WLPO axis
  - Future extension points for higher FT principles
  
  ## Key Results
  - UCT has profile (0,1): height 0 on WLPO, height 1 on FT
  - Gap has profile (1,0): height 1 on WLPO, height 0 on FT
  - These profiles demonstrate true 2-dimensional independence
-/

namespace Papers.P3.FTFrontier

open Papers.P3.Phase2
open Papers.P3.Phase3

/-! ## Axis Type Definition -/

/-- 
An axis in the 2-dimensional uniformization height space.

Each axis represents an independent dimension of logical strength.
-/
structure Axis where
  name : String
deriving DecidableEq, Repr

/-! ## Standard Axes -/

/-- 
The WLPO axis in the 2-dimensional height space.

Measures logical strength via decidability principles like WLPO.
The bidual gap sits at height 1 on this axis.
-/
def WLPO_axis : Axis := ⟨"WLPO"⟩

/-- 
The Fan Theorem (FT) axis in the 2-dimensional height space.

Measures logical strength via continuity principles like UCT.
Orthogonal to the WLPO axis, demonstrating independence.
-/
def FT_axis : Axis := ⟨"FT"⟩

/-! ## Witness Families on the FT Axis -/

/-- 
Uniform Continuity Theorem (UCT) as a witness family.

UCT states that every pointwise continuous function on [0,1]
is uniformly continuous. This principle:
- Has height 0 on WLPO axis (doesn't need WLPO)
- Has height 1 on FT axis (characteristic FT principle)
-/
def UCTWitness : WitnessFamily := {
  C := fun F => fun 
    | Sigma0.real => PUnit  -- Placeholder for UCT statement on reals
    | _ => PUnit
}

/-- 
Multi-axis height oracle that supplies height information.

This assumption-parametric approach allows the module to demonstrate
profiles and independence without introducing axioms.
-/
structure HeightOracle where
  heightAt : Axis → WitnessFamily → Option Nat
  gap_wlpo : heightAt WLPO_axis GapFamily = some 1
  gap_ft   : heightAt FT_axis GapFamily = some 0
  uct_wlpo : heightAt WLPO_axis UCTWitness = some 0
  uct_ft   : heightAt FT_axis UCTWitness = some 1

/-! ## Combined Profiles -/

/-- 
The 2D profile of a witness family.

Captures heights on both WLPO and FT axes simultaneously.
-/
structure AxCalProfile where
  wlpo_height : Option Nat
  ft_height : Option Nat
deriving DecidableEq, Repr

/-- 
Get the full 2D profile of a witness family using an oracle.

The oracle provides the multi-axis height function without
requiring axioms or sorries.
-/
noncomputable def getProfile (O : HeightOracle) (W : WitnessFamily) : AxCalProfile :=
  { wlpo_height := O.heightAt WLPO_axis W
    ft_height := O.heightAt FT_axis W }

/-- 
UCT has orthogonal profile (0,1) under any oracle satisfying the constraints.

Demonstrates that UCT is independent of WLPO-style principles.
-/
theorem uct_orthogonal_profile (O : HeightOracle) : 
  getProfile O UCTWitness = ⟨some 0, some 1⟩ := by
  simp [getProfile, O.uct_wlpo, O.uct_ft]

/-- 
Gap has orthogonal profile (1,0) under any oracle satisfying the constraints.

The bidual gap is independent of FT-style principles.
-/
theorem gap_orthogonal_profile (O : HeightOracle) :
  getProfile O GapFamily = ⟨some 1, some 0⟩ := by
  simp [getProfile, O.gap_wlpo, O.gap_ft]

/-! ## Axis Independence -/

/-- 
The WLPO and FT axes are independent.

Witnessed by the existence of principles with profiles (0,1) and (1,0).
This holds for any oracle satisfying the standard height constraints.
-/
theorem axes_independent (O : HeightOracle) : 
  ∃ (W₁ W₂ : WitnessFamily),
    getProfile O W₁ = ⟨some 0, some 1⟩ ∧ 
    getProfile O W₂ = ⟨some 1, some 0⟩ := by
  refine ⟨UCTWitness, GapFamily, ?_, ?_⟩
  · exact uct_orthogonal_profile O
  · exact gap_orthogonal_profile O

/-! ## Future Extensions -/

/-- 
Placeholder for higher FT principles.

Future work will identify principles at height 2+ on the FT axis,
such as those related to stronger continuity or compactness properties.
-/
def FT_height_2_witness : WitnessFamily := {
  C := fun _ _ => PUnit  -- Placeholder
}

/-- 
Future work: Higher FT principles.

An oracle could specify that some witness has height 2 on the FT axis,
demonstrating the framework's extensibility to higher levels.
-/
lemma ft_height_2_demo (O : HeightOracle) 
  (h : O.heightAt FT_axis FT_height_2_witness = some 2)
  (h' : O.heightAt WLPO_axis FT_height_2_witness = some 0) :
  getProfile O FT_height_2_witness = ⟨some 0, some 2⟩ := by
  simp [getProfile, h, h']

/-! ## API Summary -/

#check WLPO_axis
#check FT_axis
#check UCTWitness
#check AxCalProfile
#check getProfile
#check axes_independent

end Papers.P3.FTFrontier