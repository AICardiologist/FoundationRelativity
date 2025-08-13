-- Probe_PiLp.lean - check what's actually available
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Lp.PiLp

noncomputable section
open ENNReal

-- Test PiLp basic functionality
#check PiLp
local notation "ℓ¹" => PiLp 1 (fun _ : ℕ => ℝ)
local notation "ℓ∞" => PiLp ⊤ (fun _ : ℕ => ℝ)
#check ℓ¹
#check ℓ∞

-- Test dual space functionality
#check (ℓ¹ →L[ℝ] ℝ)
#check NormedSpace.inclusionInDoubleDual ℝ ℓ¹

-- Search for available dual-related functions
#find _ ≃ᵢ PiLp _ _
#find PiLp _ _ →L[ℝ] ℝ
#find LinearIsometryEquiv.dualMap
