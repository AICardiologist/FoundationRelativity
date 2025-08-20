import Papers.P1_GBC.RankOneToggle.Toggle
import Papers.P1_GBC.RankOneToggle.Spectrum
import Papers.P1_GBC.RankOneToggle.ShermanMorrison
import Papers.P1_GBC.RankOneToggle.Fredholm

/-!
# Tutorial: Using the Rank-One Toggle Kernel

This module provides didactic examples showing how to use the rank-one toggle
operator and its properties. Suitable for learning and teaching.

## Examples Covered
1. Constructing projections onto specific vectors
2. Computing with the toggle operator
3. Verifying spectral properties
4. Using the Sherman-Morrison formula
5. Foundation-relative behavior

## Pedagogical Notes
These examples demonstrate how Boolean parameters can encode logical choices
in functional analysis, connecting to the broader foundation-relativity theme.
-/

namespace RankOneToggle.Tutorial

open RankOneToggle ContinuousLinearMap

-- We'll work in ℓ² for concreteness
abbrev l2 := lp (fun _ : ℕ => ℝ) 2

/-- Standard basis vector e_n in ℓ² -/
noncomputable def e (n : ℕ) : l2 := lp.single 2 n 1

/-- e_n has norm 1 -/
@[simp] lemma norm_e (n : ℕ) : ‖e n‖ = 1 := by
  simp [e, lp.norm_single]

/-! ## Example 1: Basic Projection -/

/-- Projection onto the first coordinate axis -/
noncomputable def P₀ : l2 →L[ℝ] l2 := projLine (e 0) (norm_e 0)

example : P₀ (e 0) = e 0 := projLine_apply_self _ _

example : P₀ (e 1) = 0 := by
  simp [P₀, projLine_apply]
  -- e₁ ⊥ e₀ in ℓ²
  sorry

example : P₀.comp P₀ = P₀ := projLine_idem _ _

/-! ## Example 2: Toggle Operator Behavior -/

/-- Toggle operator for the first coordinate -/
noncomputable def G₀ (c : Bool) : l2 →L[ℝ] l2 := G (e 0) (norm_e 0) c

/-- When c = false, G is the identity -/
example : G₀ false = ContinuousLinearMap.id ℝ l2 := G_false _ _

/-- When c = true, G kills e₀ -/
example : G₀ true (e 0) = 0 := by
  simp [G₀, G_true, projLine_apply_self]

/-- When c = true, G preserves vectors orthogonal to e₀ -/
example : G₀ true (e 1) = e 1 := by
  have h_orth : ⟪e 0, e 1⟫_ℝ = 0 := by
    -- Orthogonality of basis vectors
    sorry
  exact has_eigenvalue_one_true (e 0) (norm_e 0) (e 1) h_orth (by sorry)

/-! ## Example 3: Spectrum Verification -/

/-- The spectrum changes with the Boolean parameter -/
example : spectrum ℝ (G₀ false) = {1} := spectrum_G_false _ _

example : spectrum ℝ (G₀ true) = {0, 1} := spectrum_G_true _ _

/-- Essential spectrum is always {1} -/
example (c : Bool) : essentialSpectrum ℝ (G₀ c) = {1} := 
  essentialSpectrum_G _ _ _

/-! ## Example 4: Sherman-Morrison Application -/

/-- Computing (I + 2P₀)⁻¹ using Sherman-Morrison -/
example : ∃ inv : l2 →L[ℝ] l2,
    inv = ContinuousLinearMap.id ℝ l2 - (2/3 : ℝ) • P₀ ∧
    inv.comp (ContinuousLinearMap.id ℝ l2 + 2 • P₀) = 
      ContinuousLinearMap.id ℝ l2 := by
  have h_proj : P₀.comp P₀ = P₀ := projLine_idem _ _
  have h_ne : (1 : ℝ) + 2 ≠ 0 := by norm_num
  obtain ⟨h_unit, h_inv⟩ := inverse_id_add_smul_proj P₀ h_proj 2 h_ne
  use ContinuousLinearMap.id ℝ l2 - (2/3 : ℝ) • P₀
  constructor
  · rfl
  · convert ← h_inv
    norm_num

/-! ## Example 5: Foundation-Relative Interpretation -/

/-- The Boolean parameter encodes a logical choice -/
def classical_case : Bool := false  -- No obstruction
def constructive_case : Bool := true  -- With obstruction

/-- In the classical case, the operator is trivial -/
example : G₀ classical_case = ContinuousLinearMap.id ℝ l2 := 
  G_false _ _

/-- In the constructive case, we get a nontrivial kernel -/
example : LinearMap.ker (G₀ constructive_case).toLinearMap = 
          Submodule.span ℝ {e 0} := 
  ker_G_true _ _

/-- Fredholm index is always 0, regardless of foundation -/
example (c : Bool) : ∃ data : FredholmData (G₀ c),
    fredholmIndex (G₀ c) data = 0 := 
  isFredholm_G _ _ _

/-! ## Example 6: Concrete Computation in ℓ² -/

/-- A concrete vector in ℓ² -/
noncomputable def v : l2 := e 0 + 2 • e 1 + 3 • e 2

/-- Computing G(true) on v -/
example : G₀ true v = 2 • e 1 + 3 • e 2 := by
  -- G(true)(e₀ + 2e₁ + 3e₂) = 0 + 2e₁ + 3e₂
  -- because G(true) kills e₀ and preserves e₁, e₂
  sorry

/-! ## Key Takeaways

1. **Projection Properties**: P² = P, P* = P, ‖P‖ = 1
2. **Toggle Behavior**: G(false) = id, G(true) = id - P
3. **Spectrum**: Changes from {1} to {0,1} based on Boolean
4. **Sherman-Morrison**: Explicit inverse formula for I + αP
5. **Fredholm Theory**: Always index 0, but dimensions change
6. **Foundation-Relativity**: Boolean encodes logical constraints

This demonstrates how simple operator theory can encode deep
logical and foundational concepts.
-/

end RankOneToggle.Tutorial