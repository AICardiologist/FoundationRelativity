import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Group.ZeroAtInfty
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

noncomputable section

-- Confirm bounded sequences
#check BoundedContinuousFunction ℕ ℝ

-- Confirm vanish at infinity space  
#check ZeroAtInftyContinuousMap ℕ ℝ

-- Find the embedding map
#find ZeroAtInftyContinuousMap ℕ ℝ → _
#find ZeroAtInftyContinuousMap _ _ → BoundedContinuousFunction _ _