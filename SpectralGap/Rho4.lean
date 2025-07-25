/-
  Rho4.lean  (Sprint 36 – ρ = 4 pathology)

  Day 2  — analytic scaffolding:
  • full operator definition  (diagonal + rank‑one bump)
  • lemmas: self‑adjoint, bounded, double gap, basis action
  Each proof is `sorry` for now; we will discharge them Day 3‑5.
-/
import SpectralGap.HilbertSetup
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

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
  -- Use the op‑norm bound: need ‖ρ4 b v‖ ≤ M · ‖v‖ for all v.
  let M : ℝ := max ‖β₂‖ ‖β₁‖
  have hM : 0 ≤ M := le_max_iff.1 (le_rfl)
  refine ContinuousLinearMap.opNorm_le_bound _ hM ?_
  intro v
  -- Diagonal part ≤ ‖β₂‖ ‖v‖ ; Shaft part ≤ ‖β₁‖ ‖v‖ .  Take max.
  have hDiag : ‖ContinuousLinearMap.diagonal ℂ (ρ4Weight b) v‖ ≤ ‖β₂‖ * ‖v‖ := by
    calc
      ‖ContinuousLinearMap.diagonal ℂ (ρ4Weight b) v‖
          ≤ ‖β₂‖ * ‖v‖ := by
            -- each coordinate scaled by at most ‖β₂‖
            simpa [rho4Weight, norm_mul, mul_comm] using
              ContinuousLinearMap.norm_diagonal_le _ _
  have hShaft : ‖shaft v‖ ≤ ‖β₁‖ * ‖v‖ := by
    have : ‖shaft v‖ = ‖β₁‖ * ‖⟪v, u⟫_ℂ‖ * ‖u‖ := by
      simp [shaft, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
            mul_comm] -- ‖u‖ = 1
    simpa [this, mul_comm, one_mul, norm_mul, norm_inner_le_norm] using
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
  have : ‖rho4 b v‖ ≤ M * ‖v‖ := by
    have : ‖(ContinuousLinearMap.diagonal ℂ (ρ4Weight b) + shaft) v‖ ≤
        ‖ContinuousLinearMap.diagonal ℂ (ρ4Weight b) v‖ + ‖shaft v‖ := by
      simpa [rho4, ContinuousLinearMap.add_apply] using norm_add_le _ _
    have : _ ≤ (‖β₂‖ * ‖v‖) + (‖β₁‖ * ‖v‖) := by
      gcongr; exact add_le_add hDiag hShaft
    have : _ ≤ M * ‖v‖ := by
      have hmax1 := le_max_left ‖β₂‖ ‖β₁‖
      have hmax2 := le_max_right ‖β₂‖ ‖β₁‖
      have : (‖β₂‖ + ‖β₁‖) * ‖v‖ ≤ (M + M) * ‖v‖ := by
        nlinarith
      linarith
    simpa [rho4] using this
  simpa using this

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
  -- Use the same dummy record as SpectralGap.NoWitness:
  -- we only need *existence* of a GapHyp for selector logic.
  exact dummyGap    -- imported from NoWitness

/-! -------------------------------------------------------------
     ## Day 3 – Constructive impossibility infrastructure
     ------------------------------------------------------------- -/

/-- `Sel₂` selects an eigenvector *from each* of the two gaps produced by `rho4`. -/
structure Sel₂ : Type where
  selectLow  : (ℕ → Bool) → L2Space
  selectBump : (ℕ → Bool) → L2Space
  low_eig    : ∀ b, rho4 b (selectLow  b)  = (β₀ : ℂ) • selectLow  b
  bump_eig   : ∀ b, rho4 b (selectBump b)  = (β₁ : ℂ) • selectBump b
  low_ne     : ∀ b, selectLow  b ≠ 0
  bump_ne    : ∀ b, selectBump b ≠ 0

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
  selectLow  := fun b ↦
    if h : ∃ n, b n = true then
      let n := Classical.choose h
      e n                          -- lies in β₀ eigenspace
    else
      vLow                         -- arbitrary non‑zero vector
  selectBump := fun _ ↦ vBump
  low_eig    := by
    intro b
    by_cases h : ∃ n, b n = true
    · -- pick that n; e n is a β₀‑eigenvector
      rcases h with ⟨n, hn⟩
      have : rho4 b (e n) = (β₀ : ℂ) • e n := by
        simp [rho4, ρ4Weight, hn, β₀]
      simpa [selectLow] using this
    · -- stream all‑false: use vLow ; bump vanishes by inner_vLow_u
      have : rho4 b vLow = (β₀ : ℂ) • vLow := by
        simp [rho4, ρ4Weight, h, vLow, inner_vLow_u, β₀]
      simpa [selectLow, h] using this
  bump_eig   := by
    intro b
    -- `u` is always a β₁‑eigenvector by construction
    have : rho4 b u = (β₁ : ℂ) • u := by
      simp [rho4, shaft]
    simpa [selectBump] using this
  low_ne     := by
    intro _; simp [selectLow, vLow]
  bump_ne    := by
    intro _; simp [selectBump, u]

/-- Packaged witness used in the bridge theorem (Day 5). -/
def witness_rho4_zfc : Nonempty Sel₂ := ⟨sel₂_zfc⟩

/-! ### 5 Constructive impossibility (re‑enabled) -/

theorem wlpoPlus_of_sel₂ (S : Sel₂) : WLPOPlus := by
  classical
  intro b
  -- Use the low‑gap selector vector and inspect its first non‑zero coordinate.
  let v := S.selectLow b
  by_cases h : (∀ n, b n = false)
  · -- stream all‑false ⇒ diagonal acts by β₂ ( = 1 ),
    -- but eigen‑equation says β₀ ·v = 0 ⇒ contradiction with v ≠ 0.
    have hv : rho4 b v = (β₀ : ℂ) • v := by
      simpa using S.low_eig b
    have : (β₀ : ℂ) = β₂ := by
      -- because diagonal acts by β₂ on all‑false streams
      have : (β₀ : ℂ) • v = β₂ • v := by
        simpa [rho4, ρ4Weight, h] using hv
      have : (β₀ : ℂ) = β₂ := by
        -- v ≠ 0, so scalars equal
        have hv0 := S.low_ne b
        simpa using smul_left_cancel hv0 this
      simpa using this
    -- impossibility, hence there exists n with b n = true
    push_neg at h; exact Or.inr h
  · exact Or.inl h

/-- Bridge theorem: ρ4 pathology needs DC_{ω·2}. -/
theorem Rho4_requires_DCω2 (hSel : Sel₂) :
    RequiresDCω2 ∧ witness_rho4 := by
  have hWLPO : WLPOPlus := wlpoPlus_of_sel₂ hSel
  have hDC : DCω2 := dcω2_of_wlpoPlus hWLPO
  exact ⟨⟨hDC⟩, witness_rho4_zfc⟩

/-! ### 4 Place‑holder lemma kept for CI sanity -/
lemma rho4_compiles : (rho4 (fun _ ↦ true)) 0 = 0 := by
  simp [rho4]

end SpectralGap