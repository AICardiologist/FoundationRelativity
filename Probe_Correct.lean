-- Probe_Correct.lean  
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Group.ZeroAtInfty
import Mathlib.Analysis.Normed.Module.Dual

noncomputable section
open ENNReal

#check PiLp
#find c0
#find dualIsometry 
#find PiLp.dualIsometry
#check LinearIsometryEquiv.dualMap
