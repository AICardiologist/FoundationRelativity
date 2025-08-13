import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.NormedSpace.C0
import Mathlib.Analysis.NormedSpace.PiLp
import Mathlib.Analysis.NormedSpace.Dual.C0
import Mathlib.Analysis.NormedSpace.Dual.PiLp

-- Probe 1: c0.dualIsometryL1
#check c0.dualIsometryL1

-- Probe 2: PiLp.dualIsometry specialized to p=1, q=∞
#check PiLp.dualIsometry

-- Probe 3: LinearIsometryEquiv.dualMap
#check LinearIsometryEquiv.dualMap
