/-
  Rho4.lean  (Sprint 36 – ρ = 4 pathology)

  Day 2  — analytic scaffolding:
  • full operator definition  (diagonal + rank‑one bump)
  • lemmas: self‑adjoint, bounded, double gap, basis action
  Each proof is `sorry` for now; we will discharge them Day 3‑5.
-/
import SpectralGap.HilbertSetup
import Mathlib.Analysis.NormedSpace.LpSpace
import Mathlib.Analysis.OperatorNorm
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.NormedSpace.InnerProduct
import Mathlib.Analysis.NormedSpace.Adjoint

open scoped ComplexReal BigOperators
open Complex Finset

namespace SpectralGap

/-! ### 0 Parameters fixed for the whole file -/
-- Low / middle / high eigenvalues (β₀ < β₁ < β₂)
def β₀ : ℝ := 0
def β₁ : ℝ := (1 : ℝ) / 2
def β₂ : ℝ := 1

lemma β₀_lt_β₁ : β₀ < β₁ := by norm_num
lemma β₁_lt_β₂ : β₁ < β₂ := by norm_num

/-! ### 1 Helper functions -/

/-- Boolean‐controlled real weights (low vs high). -/
noncomputable def ρ4Weight (b : ℕ → Bool) (n : ℕ) : ℝ :=
  if b n then β₀ else β₂

/-- Rank‑one bump vector `u` with square‑summable coefficients `2^{-(n+1)}`. -/
noncomputable
def u : L2Space :=
by
  -- quick construction with `lp.single` + `summable_pow_2`
  refine
    ⟨fun n ↦ (2 : ℂ) ^ (-(n : ℤ)-1), ?_⟩
  -- summability proof left `sorry` for Day 4 clean‑up
  sorry

/-- Rank‑one compact "shaft" sending `v ↦ ⟪v,u⟫ • u` and then rescaling to β₁. -/
noncomputable
def shaft : BoundedOp :=
  (ContinuousLinearMap.smulRight
      (ContinuousLinearMap.innerSL ℂ).toContinuousLinearMap
      (β₁ : ℂ)).comp
    (ContinuousLinearMap.const _ _)

/-! ### 2 Main operator -/

/-- **ρ4** : diagonal (controlled by `b`) + rank‑one bump. -/
noncomputable
def rho4 (b : ℕ → Bool) : BoundedOp :=
  ContinuousLinearMap.diagonal ℂ (ρ4Weight b) +
  shaft

/-! ### 3 Analytic lemmas (proofs `sorry` for now) -/

lemma rho4_selfAdjoint (b : ℕ → Bool) :
    IsSelfAdjoint (rho4 b) := by
  sorry

lemma rho4_bounded (b : ℕ → Bool) :
    ‖rho4 b‖ ≤ max ‖β₂‖ ‖β₁‖ := by
  sorry

/-- Action on basis vectors `e n` (ignoring bump, which is rank‑one). -/
lemma rho4_apply_basis (b : ℕ → Bool) (n : ℕ) :
    rho4 b (e n) = (if b n then (β₀ : ℂ) else β₂) • e n + (β₁ : ℂ) •
      ((e n).inner u) • u := by
  sorry

/-- Double spectral gap: low versus bump, bump versus high. -/
lemma rho4_has_two_gaps (b : ℕ → Bool) :
    selHasGap (rho4 b) := by
  /- Provide the structure `GapHyp` with
       a := β₀ + 1/4,  b := β₁ - 1/4,
       a₂ := β₁ + 1/4, b₂ := β₂ - 1/4
     and verify inequalities + gap conditions. -/
  sorry

/-! -------------------------------------------------------------
     ## Day 3 – Constructive impossibility infrastructure
     ------------------------------------------------------------- -/

/-- `Sel₂` selects an eigenvector *from each* of the two gaps produced by `rho4`. -/
structure Sel₂ : Type where
  /-- given any Boolean stream `b`, produce a vector in the low gap -/
  selectLow  : (ℕ → Bool) → L2Space
  selectBump : (ℕ → Bool) → L2Space
  low_eig    : ∀ b, rho4 b (selectLow  b)  = (β₀ : ℂ) • selectLow  b
  bump_eig   : ∀ b, rho4 b (selectBump b)  = (β₁ : ℂ) • selectBump b
  low_ne     : ∀ b, selectLow  b ≠ 0
  bump_ne    : ∀ b, selectBump b ≠ 0

/-- **Constructive impossibility.**  
    A selector for *both* gaps is strong enough to decide WLPO⁺, hence DC_{ω·2}. -/
theorem wlpoPlus_of_sel₂ (hSel : Sel₂) : WLPOPlus := by
  /- **Idea (outline, proof tomorrow):**
     • Read `hSel.b` boolean stream.
     • If `∃ n, hSel.b n = true` we show ... else ...
     This reproduces Cheeger logic twice and upgrades to WLPO⁺. -/
  sorry

/-- Bridge to DC_{ω·2}.  Provided for Day 5 proof chain. -/
theorem dcω2_of_wlpoPlus (h : WLPOPlus) : DCω2 := by
  -- Already available in `SpectralGap.LogicDSL`, but repeat signature here.
  exact LogicDSL.dcω2_of_wlpoPlus h

/-! ### 4 Place‑holder lemma kept for CI sanity -/
lemma rho4_compiles : (rho4 (fun _ ↦ true)) 0 = 0 := by
  simp [rho4]

end SpectralGap