import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Group.ZeroAtInfty
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Lp.Dual.Pi

noncomputable section
open ENNReal

-- Use arrow notation; do NOT write C₀(ℕ, ℝ)
abbrev c0  := (ℕ →C₀ ℝ)
abbrev l1  := PiLp 1 (fun _ : ℕ => ℝ)
abbrev linf := PiLp ∞ (fun _ : ℕ => ℝ)

-- Sanity
#check PiLp
#check (ℕ →C₀ ℝ)

-- (c₀)* ≃ᵢ ℓ¹
#check ZeroAtInftyContinuousMap.dualIsometryLp1

-- (ℓ¹)* ≃ᵢ ℓ∞  (symbol presence check)
#check PiLp.dualIsometry

-- Dual map API (post‑refactor)
#check ContinuousLinearEquiv.dualMap
#check LinearEquiv.dualMap