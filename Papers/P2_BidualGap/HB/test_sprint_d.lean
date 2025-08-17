/-
Acceptance tests for Sprint D implementation
-/

import Papers.P2_BidualGap.HB.DualIsometriesComplete

namespace Papers.P2.HB.Tests

open Papers.P2.HB.GenericIndex

variable {ι : Type*} [DecidableEq ι] [TopologicalSpace ι] [DiscreteTopology ι]

-- Test D1: summable_abs_eval compiles and has right type
example (f : c₀ →L[ℝ] ℝ) : Summable (fun n : ι => |f (e n)|) := 
  summable_abs_eval f

-- Test D2: CLM_ext_basis compiles and proves equality
example (f g : c₀ →L[ℝ] ℝ) (h : ∀ i, f (e i) = g (e i)) : f = g :=
  CLM_ext_basis h

-- Test D3: toCoeffsL1_injective shows injectivity
example : Function.Injective (@toCoeffsL1 ι _ _ _) :=
  toCoeffsL1_injective

-- Test D4: norm preservation for the isometry
example (f : c₀ →L[ℝ] ℝ) : ‖toCoeffsL1 f‖ = ‖f‖ :=
  norm_toCoeffsL1 f

-- Test: The main isometry exists and type-checks
example : (c₀ →L[ℝ] ℝ) ≃ₗᵢ[ℝ] lp (fun _ : ι => ℝ) 1 :=
  dual_c0_iso_l1

end Papers.P2.HB.Tests