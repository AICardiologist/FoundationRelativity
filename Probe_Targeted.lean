-- Probe_Targeted.lean  
import Mathlib.Analysis.NormedSpace.PiLp
import Mathlib.Analysis.NormedSpace.ZeroAtInfty
import Mathlib.Analysis.NormedSpace.Dual

noncomputable section
open ENNReal

#check PiLp
#check ZeroAtInftyBoundedLinearMaps
#check c0
#find dualIsometry
#find PiLp.dualIsometry
#check LinearIsometryEquiv.dualMap
