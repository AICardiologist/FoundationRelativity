-- Probe_All.lean
import Mathlib

noncomputable section
open ENNReal

#check PiLp
#check c0
#find dualIsometry
#find (c0 _ _) →L[ℝ] ℝ ≃ᵢ _
#find PiLp _ _ →L[ℝ] ℝ
#check LinearIsometryEquiv.dualMap
