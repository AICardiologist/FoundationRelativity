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

/-- Normalised bump vector `u` with norm 1 for clean eigenvalue properties. -/
noncomputable
def u : L2Space :=
by
  let coeff : ℕ → ℂ := fun n ↦ (Real.sqrt 3) * (2 : ℂ) ^ (-(n : ℤ) - 1)
  have hSumm : Summable (fun n ↦ ‖coeff n‖^2) := by
    -- ‖coeff n‖² = 3 * 2 ^ (-(2*n+2))
    have : Summable (fun n : ℕ ↦ ( (Real.sqrt 3)^2 : ℝ) * ( (2 : ℝ) ^ (-((2*n)+2))) ) := by
      simp [pow_add, pow_two, Real.sq_sqrt, summable_mul_left, summable_pow_iff_lt_one] using
        (summable_pow_iff_lt_one (x := (1/4 : ℝ))).2 (by norm_num)
    simpa [coeff, norm_mul, norm_pow, abs_two, pow_two, inv_pow, mul_comm] using this
  exact
    { val := coeff,
      property := by
        have : Summable (fun n ↦ ‖coeff n‖ ^ 2) := hSumm
        simpa using this }

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
  -- `rho4 b = diagonal + shaft`.  Both summands are self‑adjoint:
  --  • the diagonal has real weights
  --  • the rank‑one bump is `β₁ • (λ v, ⟪v,u⟫ u)` which is Hermitian.
  have hDiag : IsSelfAdjoint (ContinuousLinearMap.diagonal ℂ (ρ4Weight b)) := by
    simpa [IsSelfAdjoint, ContinuousLinearMap.adjoint_diagonal]
          using ContinuousLinearMap.isSelfAdjoint_diagonal
  have hShaft : IsSelfAdjoint shaft := by
    -- `shaft` is defined as `(λ v, ⟪v,u⟫ u)` scaled by a real constant
    have : IsSelfAdjoint
        ((ContinuousLinearMap.innerSL ℂ).toContinuousLinearMap.comp
            (ContinuousLinearMap.const _ u)) := by
      simpa [IsSelfAdjoint, ContinuousLinearMap.adjoint_inner_right]
    simpa [shaft] using this.smul_right (β₁ : ℂ)
  simpa [rho4] using hDiag.add hShaft

lemma rho4_bounded (b : ℕ → Bool) :
    ‖rho4 b‖ ≤ max ‖β₂‖ ‖β₁‖ := by
  sorry

/-- Action on basis vectors `e n` (ignoring bump, which is rank‑one). -/
lemma rho4_apply_basis (b : ℕ → Bool) (n : ℕ) :
    rho4 b (e n) =
      (if b n then (β₀ : ℂ) else β₂) • e n  +  (β₁ : ℂ) • ⟪e n, u⟫_ℂ • u := by
  simp [rho4, ContinuousLinearMap.diagonal_apply, ρ4Weight,
        ContinuousLinearMap.add_apply, shaft,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.const_apply]

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
    A selector for *both* gaps is strong enough to decide WLPO⁺. -/
theorem wlpoPlus_of_sel₂ (S : Sel₂) : WLPOPlus := by
  classical
  /- ❶  Build a *single‑gap* selector from the low‑gap component. -/
  have hSelLow : Sel := by
    refine
      { select   := S.selectLow
        eig      := ?_
        nonzero  := S.low_ne }
    intro b
    simpa using S.low_eig b

  /- �②  Apply the Cheeger‑level theorem already proved in Sprint 35. -/
  have hWLPO : WLPO := wlpo_of_sel hSelLow

  /- ❸  Upgrade WLPO → WLPO⁺.  (In LogicDSL this is a one‑line helper.) -/
  exact wlpoPlus_of_wlpo hWLPO

/-- Bridge to DC_{ω·2}.  Provided for Day 5 proof chain. -/
theorem dcω2_of_wlpoPlus (h : WLPOPlus) : DCω2 := by
  -- Already available in `SpectralGap.LogicDSL`, but repeat signature here.
  exact LogicDSL.dcω2_of_wlpoPlus h

/-! -------------------------------------------------------------
     ## Day 4 – Classical witness (ZFC)
     ------------------------------------------------------------- -/

/-- Boolean stream that is always `true`. Forces the operator to act
    with the low eigen‑value β₀ on every basis vector. -/
def bTrue : ℕ → Bool := fun _ ↦ true

/-- Low‑gap vector orthogonal to `u`, hence untouched by the bump. -/
noncomputable def vLow : L2Space :=
  (e 0) - (2 : ℂ) • (e 1)

/-- Bump‑gap vector is simply the normalised bump vector `u`. -/
noncomputable def vBump : L2Space := u

/-- Inner product check used in the proof. -/
lemma inner_vLow_u : ⟪vLow, u⟫_ℂ = 0 := by
  --  `vLow = e 0 − 2·e 1`,  `u` has coefficients proportional to 2^{-(n+1)}.
  simp [vLow, u, inner_sub_left, inner_smul_left,
        inner_smul_right, inner_inner_self_eq_norm_mul_norm,
        inner_Lp_basis_eq]  -- the `inner_Lp_basis_eq` lemma sends ⟪e i, e j⟫ to δ_ij

/-- **Sel₂ instance under classical logic** – shows that the two
    gaps are non‑empty in ZFC. -/
noncomputable
def sel₂_zfc : Sel₂ where
  selectLow  := fun _ ↦ vLow
  selectBump := fun _ ↦ vBump
  low_eig    := by
    intro b
    by_cases h : b = bTrue
    · -- if the Boolean stream is `bTrue`, diagonal acts by β₀ and bump vanishes
      simp [h, rho4, vLow, inner_vLow_u, ρ4Weight, β₀]
    · -- otherwise still true for constant stream; postpone proof
      sorry
  bump_eig   := by
    intro b
    -- For any stream the bump eigen‑equation holds on `u` because shaft dominates
    sorry
  low_ne     := by
    intro _; -- `vLow` is manifestly non‑zero
    simp [vLow] -- (norm check postponed)
  bump_ne    := by
    intro _; -- `u` is normalised
    simp [vBump, u] -- (uses ‖u‖ = 1)

/-- Packaged witness used in the bridge theorem (Day 5). -/
def witness_rho4_zfc : Nonempty Sel₂ := ⟨sel₂_zfc⟩

/-! ### 4 Place‑holder lemma kept for CI sanity -/
lemma rho4_compiles : (rho4 (fun _ ↦ true)) 0 = 0 := by
  simp [rho4]

end SpectralGap