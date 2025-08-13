-- Probe_Final.lean  
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Group.ZeroAtInfty  
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

noncomputable section
open ENNReal ZeroAtInfty

-- Test the key components
#check PiLp
#check ZeroAtInftyContinuousMap ℕ ℝ  -- This should be our c₀
#check C₀(ℕ, ℝ)  -- Alternative notation

-- Search for duality results
#find PiLp _ _ →L[ℝ] ℝ ≃ᵢ _
#find dualIsometry
#find LinearIsometryEquiv.dualMap

-- Test ENNReal conjugate
#find ENNReal.IsConjExponent

-- Test basic operations
#check (1 : ENNReal)
#check (⊤ : ENNReal)
