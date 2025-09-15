/-
Paper 5: General Relativity AxCal Analysis - Smoke Test
CI aggregator and verification guard for all GR AxCal components
-/

import Papers.P5_GeneralRelativity.AxCalCore.Axis
import Papers.P5_GeneralRelativity.AxCalCore.Tokens
import Papers.P5_GeneralRelativity.AxCalCore.ProfileLUB
import Papers.P5_GeneralRelativity.GR.Portals
import Papers.P5_GeneralRelativity.GR.ComposeLaws
import Papers.P5_GeneralRelativity.GR.Compose
import Papers.P5_GeneralRelativity.GR.EPSCore
import Papers.P5_GeneralRelativity.GR.Schwarzschild
import Mathlib.Tactic  -- for `norm_num` in tiny numeric examples

namespace Paper5Smoke
open Papers.P5_GeneralRelativity
open AxisProfile

#check Height
#check AxisProfile
#check PortalFlag
#check route_to_profile

theorem route_to_profile_sanity :
  (route_to_profile [PortalFlag.uses_zorn]).hChoice = Height.one ∧
  (route_to_profile [PortalFlag.uses_limit_curve]).hComp = Height.one ∧
  (route_to_profile [PortalFlag.uses_serial_chain]).hChoice = Height.one ∧
  (route_to_profile [PortalFlag.uses_reductio]).hLogic = Height.one := by
  constructor
  · simp [route_to_profile, memFlag, eqb]   -- Zorn → Choice
  constructor
  · simp [route_to_profile, memFlag, eqb]   -- Limit-curve → Comp
  constructor
  · simp [route_to_profile, memFlag, eqb]   -- Serial-chain (DCω) → Choice
  · simp [route_to_profile, memFlag, eqb]   -- Reductio → Logic

#check maxH
#check maxAP
#check maxH_comm
#check maxH_assoc
#check maxH_idem
#check maxAP_comm
#check maxAP_assoc
#check maxAP_idem

#check route_to_profile_append_eq_maxAP
#check composition_associative
#check composition_commutative
#check composition_idempotent

#check LocalPDE_Profile
#check MGHD_Profile
#check G2_Composed_Profile
#check G2_Composed_profile_law
#check G2_Composed_well_formed

#reduce route_to_profile (LocalPDE_flags ++ MGHD_flags)

theorem Belt_and_Suspenders_Normalization_Check :
  route_to_profile (LocalPDE_flags ++ MGHD_flags) = 
  AxisProfile.mk Height.one Height.one Height.zero := by
  simp [LocalPDE_flags, MGHD_flags, route_to_profile, memFlag, eqb]

section EPSSmokeChecks
open EPS

#check LightRay
#check FreeFall  
#check WeylConnection
#check EPS_CompatibilityData
#check EPS_Implementation
#check EPS_DerivationSteps
#check EPS_Algorithm
#check Kinematics
#check derive_metric

theorem EPS_constructive_witnesses_are_PUnit (S : Spacetime) :
  (∀ lr : LightRay S, lr.is_null = PUnit.unit ∧ lr.is_geodesic = PUnit.unit) ∧
  (∀ ff : FreeFall S, ff.is_timelike = PUnit.unit ∧ ff.is_geodesic = PUnit.unit) ∧
  (∀ W : WeylConnection S, W.preserves_conformal = PUnit.unit ∧ W.torsion_free = PUnit.unit) := by
  constructor
  · intro lr; exact ⟨rfl, rfl⟩
  constructor
  · intro ff; exact ⟨rfl, rfl⟩
  · intro W; cases W; exact ⟨rfl, rfl⟩

theorem EPS_compatibility_preserves_all (S : Spacetime) :
  ∀ (compat : EPS_CompatibilityData S) (lr : LightRay S) (ff : FreeFall S),
    compat.preserves_light lr = PUnit.unit ∧ compat.preserves_geodes ff = PUnit.unit := by
  intros; exact ⟨rfl, rfl⟩

theorem ScaleIntegrable_always_holds (S : Spacetime) :
  ∀ W : WeylConnection S, ScaleIntegrable W := by
  exact ScaleIntegrable_always

#check EPS_Height_Zero
#check EPS_Height_Zero_Structured
#check EPS_Lorentz_Recovery
#check EPS_Kinematics_Height0

end EPSSmokeChecks

section SchwarzschildSmokeChecks
open Schwarzschild

#check SchwarzschildCoords
#check f
#check f_pos_of_hr
#check f_derivative
#check g_tt
#check g_rr
#check g_θθ
#check g_φφ
#check g_inv_tt
#check g_inv_rr
#check Γ_t_tr
#check Γ_r_tt
#check Γ_r_rr
#check Christoffel_t_tr_formula
#check Christoffel_r_tt_nonzero

-- Verify that f(r) has the correct form
theorem f_formula_check (M r : ℝ) :
  f M r = 1 - 2*M/r := by
  rfl  -- definitional equality

-- Verify metric components use f correctly
theorem metric_uses_f (M r : ℝ) :
  g_tt M r = -f M r ∧ g_rr M r = (f M r)⁻¹ := by
  constructor <;> rfl

-- Verify inverse metric relationship
theorem inverse_metric_check (M r : ℝ) :
  g_inv_rr M r = f M r ∧ g_inv_tt M r = -(f M r)⁻¹ := by
  constructor <;> rfl

-- Check a specific Christoffel symbol value
example (M r : ℝ) : Γ_t_tr M r = M / (r^2 * f M r) := by
  rfl

-- Concrete numeric sanity checks (no calculus, tiny and fast):
-- With M = 1, r = 3, θ arbitrary, we have f(1,3) = 1 - 2/3 > 0
example : 0 < f (1 : ℝ) (3 : ℝ) := by
  have hM : 0 < (1 : ℝ) := by norm_num
  have hr : 2 * (1 : ℝ) < (3 : ℝ) := by norm_num
  exact Schwarzschild.f_pos_of_hr (1 : ℝ) (3 : ℝ) hM hr

-- And Γ^r_{tt}(1,3) ≠ 0 via the proved inequality lemma
example : Γ_r_tt (1 : ℝ) (3 : ℝ) ≠ 0 := by
  have hM : 0 < (1 : ℝ) := by norm_num
  have hr : 2 * (1 : ℝ) < (3 : ℝ) := by norm_num
  exact Schwarzschild.Christoffel_r_tt_nonzero (1 : ℝ) (3 : ℝ) hM hr

end SchwarzschildSmokeChecks

def Paper5_Smoke_Success : True := True.intro

end Paper5Smoke