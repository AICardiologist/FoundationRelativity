/- ProbeDualAPI.lean : confirm dual-chain API exists on pinned mathlib -/
import Mathlib.Analysis.NormedSpace.C0
import Mathlib.Analysis.NormedSpace.PiLp
import Mathlib.Analysis.NormedSpace.Dual.C0
import Mathlib.Analysis.NormedSpace.Dual.PiLp
import Mathlib.Analysis.Normed.Module.Dual

noncomputable section
open ENNReal

/-- Local notations for readability -/
local notation "c₀" => c0 ℕ ℝ
local notation "ℓ¹" => PiLp (1 : ℝ≥0∞) (fun _ : ℕ => ℝ)
local notation "ℓ∞" => PiLp (⊤ : ℝ≥0∞) (fun _ : ℕ => ℝ)

/-- 1) (c₀)* ≃ᵢ ℓ¹ -/
#check c0.dualIsometryL1 (R := ℝ) (ι := ℕ)

/-- 2) (ℓ¹)* ≃ᵢ ℓ∞ (p=1, q=∞; conjugate exponents) -/
lemma _hCE : (1 : ℝ≥0∞).IsConjExponent ⊤ := ENNReal.isConjExponent_one_top
#check PiLp.dualIsometry (R := ℝ) (β := fun _ : ℕ => ℝ)
                        (p := (1 : ℝ≥0∞)) (q := (⊤ : ℝ≥0∞))
                        le_rfl le_top _hCE

/-- 3) Dual map on isometry equivalences -/
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
                        [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (e : E ≃ᵢ[ℝ] F)
#check e.dualMap
