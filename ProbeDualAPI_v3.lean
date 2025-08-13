import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Group.ZeroAtInfty
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-- Minimal probe for c₀/ℓᵖ duality under the Lp refactor (Aug 2025). -/

open ENNReal
open ZeroAtInftyContinuousMap

noncomputable section

-- Local notations:
local notation "c₀" => C₀(ℕ, ℝ)
local notation "ℓ¹" => PiLp 1 (fun _ : ℕ => ℝ)
local notation "ℓ∞" => PiLp ∞ (fun _ : ℕ => ℝ)

-- 1) (c₀)* ≃ᵢ ℓ¹
#check ZeroAtInftyContinuousMap.dualIsometryLp1 (R := ℝ) (ι := ℕ)
-- Expected: (C₀(ℕ, ℝ) →L[ℝ] ℝ) ≃ᵢ[ℝ] PiLp 1 (fun _ => ℝ)

-- 2) (ℓ¹)* ≃ᵢ ℓ∞ (conjugate exponents 1 and ∞)
lemma h_conj : (1 : ENNReal).IsConjExponent ∞ := ENNReal.isConjExponent_one_top
#check PiLp.dualIsometry (R := ℝ) (β := (fun _ : ℕ => ℝ))
                          (p := 1) (q := ∞) le_rfl le_top h_conj
-- Expected: (ℓ¹ →L[ℝ] ℝ) ≃ᵢ[ℝ] ℓ∞

-- 3) dual map lives on ContinuousLinearEquiv now (not LinearIsometryEquiv)
variables {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
variables [NormedSpace ℝ E] [NormedSpace ℝ F]
variable (e : E ≃ᵢ[ℝ] F)
#check e.toContinuousLinearEquiv.dualMap
-- Expected: (F →L[ℝ] ℝ) ≃L[ℝ] (E →L[ℝ] ℝ)
