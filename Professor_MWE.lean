-- Core Imports (Definitions of the spaces and basic dual API)
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Group.ZeroAtInfty
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

-- >>> CRUCIAL IMPORT FOR DUALITY THEOREMS <<<
-- This module should contain the duality results for Pi-type Lp spaces.
import Mathlib.Analysis.Normed.Lp.Dual.Pi

-- Namespaces
open ZeroAtInftyContinuousMap
open ENNReal

noncomputable section

-- Local Notations
local notation "c₀" => C₀(ℕ, ℝ)
local notation "ℓ¹" => PiLp 1 (fun _ : ℕ => ℝ)
local notation "ℓ∞" => PiLp ∞ (fun _ : ℕ => ℝ)

/-
Q3.1: (c₀)* ≃ᵢ ℓ¹
Current Name: ZeroAtInftyContinuousMap.dualIsometryLp1
We use #check? to tentatively probe if the symbol is found after the import.
-/
#check? ZeroAtInftyContinuousMap.dualIsometryLp1 (R := ℝ) (ι := ℕ)
-- Expected: (C₀(ℕ, ℝ) →L[ℝ] ℝ) ≃ᵢ[ℝ] PiLp 1 fun x => ℝ

/-
Q3.2: (ℓ¹)* ≃ᵢ ℓ∞
Current Name: PiLp.dualIsometry
-/
-- Proof that 1 and ∞ are conjugate exponents
lemma h_conj : (1 : ENNReal).IsConjExponent ∞ := ENNReal.isConjExponent_one_top

-- Specialization for p=1, q=∞.
#check? PiLp.dualIsometry (R := ℝ) (β := (fun _ : ℕ => ℝ)) (p := 1) (q := ∞) le_rfl le_top h_conj
-- Expected: (PiLp 1 (fun x => ℝ) →L[ℝ] ℝ) ≃ᵢ[ℝ] PiLp ∞ fun x => ℝ

/-
Q3.3: Dual Map on Equivalences
Current API: ContinuousLinearEquiv.dualMap
(LinearIsometryEquiv.dualMap has been removed).
-/
variables {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
variables [NormedSpace ℝ E] [NormedSpace ℝ F]
variable (e : E ≃ᵢ[ℝ] F)

-- We use the dualMap from the ContinuousLinearEquiv derived from the isometry.
#check e.toContinuousLinearEquiv.dualMap
-- Expected: (F →L[ℝ] ℝ) ≃L[ℝ] (E →L[ℝ] ℝ)

end