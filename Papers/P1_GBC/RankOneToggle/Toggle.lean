import Papers.P1_GBC.RankOneToggle.Projection
import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# Rank-One Toggle Operator

This module defines the rank-one toggle operator G(c) := id - c·P where c ∈ {false, true}
and P is a rank-one projection onto a line in a Hilbert space.

## Main Definitions
- `G`: The toggle operator parameterized by a Boolean
- Kernel and range characterizations
- Injectivity and surjectivity equivalences

## Implementation Notes
- The Boolean parameter encodes logical choices in a foundation-relative way
- When c = false, G = id (identity operator)
- When c = true, G = id - P (complementary projection)

## Mathematical Significance
This operator demonstrates how Boolean parameters can encode foundation-dependent
behavior in functional analysis, connecting to the broader foundation-relativity theme.
-/

namespace RankOneToggle

open ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Rank-one toggle operator G(c) := id - (if c then 1 else 0) • P. -/
noncomputable def G (u : H) (hu : ‖u‖ = 1) (c : Bool) : H →L[𝕜] H :=
  ContinuousLinearMap.id 𝕜 H - (if c then (1 : 𝕜) else 0) • projLine (𝕜 := 𝕜) u hu

@[simp]
lemma G_false (u : H) (hu : ‖u‖ = 1) :
    G u hu false = ContinuousLinearMap.id 𝕜 H := by
  simp [G]

@[simp]
lemma G_true (u : H) (hu : ‖u‖ = 1) :
    G u hu true = ContinuousLinearMap.id 𝕜 H - projLine (𝕜 := 𝕜) u hu := by
  simp [G]

section props
variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

lemma ker_G_true (u : H) (hu : ‖u‖ = 1) :
    LinearMap.ker (G (𝕜 := 𝕜) u hu true).toLinearMap = Submodule.span 𝕜 {u} := by
  ext x
  constructor
  · -- x in ker(id - P) ⇒ x = P x ⇒ x ∈ range P = span{u}
    intro hx
    have hx0 : G (𝕜 := 𝕜) u hu true x = 0 := by
      simpa [LinearMap.mem_ker] using hx
    have hxeq : x = (projLine (𝕜 := 𝕜) u hu) x := by
      simpa [G_true, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero] using hx0
    have hxrange : x ∈ LinearMap.range (projLine (𝕜 := 𝕜) u hu).toLinearMap := ⟨x, hxeq.symm⟩
    rw [range_projLine (𝕜 := 𝕜) u hu] at hxrange
    exact hxrange
  · -- x ∈ span{u} ⇒ (id - P) x = 0
    intro hx
    rcases Submodule.mem_span_singleton.mp hx with ⟨c, rfl⟩
    simp [LinearMap.mem_ker, G_true, projLine_apply, inner_self_eq_norm_sq_to_K, hu]

lemma range_G_true (u : H) (hu : ‖u‖ = 1) :
    LinearMap.range (G (𝕜 := 𝕜) u hu true).toLinearMap = (Submodule.span 𝕜 {u})ᗮ := by
  ext x
  constructor
  · -- y ↦ (id - P) y is orthogonal to u
    rintro ⟨y, rfl⟩
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    simp only [ContinuousLinearMap.coe_coe, G_true, ContinuousLinearMap.sub_apply, 
               ContinuousLinearMap.id_apply]
    -- Need to show ⟪y - P(y), u⟫ = 0
    rw [inner_sub_left]
    -- ⟪y, u⟫ - ⟪P(y), u⟫ = ⟪y, u⟫ - ⟪y, u⟫ = 0
    -- Use the fact that ⟪P(y), u⟫ = ⟪⟪u,y⟫ • u, u⟫ = ⟪u,y⟫ * ⟪u,u⟫ = ⟪u,y⟫
    rw [projLine_apply, inner_smul_left]
    simp [inner_self_eq_norm_sq_to_K, hu]
  · -- if ⟪u,x⟫ = 0 then (id - P) x = x
    intro hx
    have hx0 : inner (𝕜 := 𝕜) u x = 0 := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at hx
      rw [← inner_conj_symm, hx]
      simp
    refine ⟨x, ?_⟩
    simp only [ContinuousLinearMap.coe_coe, G_true, ContinuousLinearMap.sub_apply, 
               ContinuousLinearMap.id_apply, projLine_apply]
    rw [hx0]
    simp

@[simp] lemma ker_G_false (u : H) (hu : ‖u‖ = 1) :
    LinearMap.ker (G (𝕜 := 𝕜) u hu false).toLinearMap = ⊥ := by
  simp [G_false, LinearMap.ker_id]

@[simp] lemma range_G_false (u : H) (hu : ‖u‖ = 1) :
    LinearMap.range (G (𝕜 := 𝕜) u hu false).toLinearMap = ⊤ := by
  simp [G_false, LinearMap.range_id]

lemma G_true_idem (u : H) (hu : ‖u‖ = 1) :
    (G (𝕜 := 𝕜) u hu true).comp (G (𝕜 := 𝕜) u hu true) = G (𝕜 := 𝕜) u hu true := by
  -- (id - P) ∘ (id - P) = id - 2P + P² = id - 2P + P = id - P
  ext x
  simp only [ContinuousLinearMap.comp_apply, G_true, ContinuousLinearMap.sub_apply,
             ContinuousLinearMap.id_apply]
  -- We need to show (x - P x) - P (x - P x) = x - P x
  -- P (x - P x) = P x - P (P x) = P x - P x = 0 (since P² = P)
  have hp2 : (projLine (𝕜 := 𝕜) u hu) ((projLine (𝕜 := 𝕜) u hu) x) = (projLine (𝕜 := 𝕜) u hu) x := by
    rw [← ContinuousLinearMap.comp_apply, projLine_idem (𝕜 := 𝕜) u hu]
  -- Now show: (x - P x) - P (x - P x) = x - P x
  -- P is linear, so P(x - P x) = P x - P(P x) = P x - P x = 0
  have : (projLine (𝕜 := 𝕜) u hu) (x - (projLine (𝕜 := 𝕜) u hu) x) = 0 := by
    rw [map_sub, hp2, sub_self]
  rw [this, sub_zero]

/-- G is injective if and only if c = false -/
theorem injective_iff (u : H) (hu : ‖u‖ = 1) (c : Bool) :
    Function.Injective (G (𝕜 := 𝕜) u hu c) ↔ c = false := by
  constructor
  · intro h
    -- If G is injective, then ker(G) = {0}
    cases c
    · rfl
    · -- c = true case: ker(G) = span{u} ≠ {0}, contradiction
      exfalso
      -- u ∈ ker(G true) but u ≠ 0
      have : (G (𝕜 := 𝕜) u hu true) u = 0 := by
        simp only [G_true, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
        rw [projLine_apply_self (𝕜 := 𝕜) u hu]
        simp
      have hu_ne : u ≠ 0 := fun h_eq => by simp [h_eq, norm_zero] at hu
      -- h says G is injective, so if G u = G 0 then u = 0
      have G_zero : (G (𝕜 := 𝕜) u hu true) 0 = 0 := by simp
      have : u = 0 := h (by rw [this, G_zero])
      exact hu_ne this
  · intro h
    rw [h]
    simp [G_false]
    exact Function.injective_id

/-- G is surjective if and only if c = false -/
theorem surjective_iff (u : H) (hu : ‖u‖ = 1) (c : Bool) :
    Function.Surjective (G (𝕜 := 𝕜) u hu c) ↔ c = false := by
  constructor
  · intro h
    cases c
    · rfl
    · -- c = true case: range(G) = span{u}^⊥ ≠ H (for nontrivial H), contradiction
      exfalso
      -- u is not in range(G true) = span{u}^⊥
      have h_range := range_G_true (𝕜 := 𝕜) u hu
      have hu_not_in_range : u ∉ LinearMap.range (G (𝕜 := 𝕜) u hu true).toLinearMap := by
        rw [h_range, Submodule.mem_orthogonal_singleton_iff_inner_left]
        rw [inner_self_eq_norm_sq_to_K, hu]
        simp
      -- But by surjectivity, u should be in the range
      obtain ⟨y, hy⟩ := h u
      exact hu_not_in_range ⟨y, hy⟩
  · intro h
    rw [h]
    simp [G_false]
    exact Function.surjective_id

/-- Fredholm alternative: For the toggle operator, injectivity ↔ surjectivity -/
theorem G_inj_iff_surj (u : H) (hu : ‖u‖ = 1) (c : Bool) :
    Function.Injective (G (𝕜 := 𝕜) u hu c) ↔ Function.Surjective (G (𝕜 := 𝕜) u hu c) := by
  rw [injective_iff, surjective_iff]

/-- Block decomposition: H = ker(G) ⊕ range(G) when c = true -/
lemma block_decomposition_true (u : H) (hu : ‖u‖ = 1) [CompleteSpace H] :
    LinearMap.ker (G (𝕜 := 𝕜) u hu true).toLinearMap ⊔ LinearMap.range (G (𝕜 := 𝕜) u hu true).toLinearMap = ⊤ := by
  -- ker(G) = span{u} and range(G) = span{u}^⊥
  -- H = span{u} ⊕ span{u}^⊥ for complete spaces
  rw [ker_G_true, range_G_true]
  -- The orthogonal decomposition theorem states that H = V ⊕ V^⊥ for any closed subspace V
  -- Here V = span{u} is closed (finite-dimensional), so H = span{u} ⊔ span{u}^⊥
  ext x
  simp only [Submodule.mem_sup, Submodule.mem_top]
  constructor
  · intro _; trivial
  · intro _
    -- Every x ∈ H can be written as x = projection onto span{u} + projection onto span{u}^⊥
    refine ⟨inner (𝕜 := 𝕜) u x • u, ?_, x - inner (𝕜 := 𝕜) u x • u, ?_, ?_⟩
    · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    · -- Show x - ⟪u, x⟫ • u ∈ span{u}^⊥
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
      rw [inner_sub_left, inner_smul_left]
      simp [inner_self_eq_norm_sq_to_K, hu]
    · -- Show x = ⟪u, x⟫ • u + (x - ⟪u, x⟫ • u)
      simp

/-! ## Block Form Analysis -/

/-- Block form decomposition: For v = α•u + w where w ⊥ u, G(true) maps v ↦ w.
    This shows G(true) acts as "0 ⊕ id" on the decomposition H = span{u} ⊕ (span{u})⊥. -/
lemma G_true_block_form (u : H) (hu : ‖u‖ = 1) (α : 𝕜) (w : H) 
    (hw : inner (𝕜 := 𝕜) u w = 0) :
    G (𝕜 := 𝕜) u hu true (α • u + w) = w := by
  -- G(true) = id - P, so G(α•u + w) = (α•u + w) - P(α•u + w)
  simp only [G_true, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  -- P is linear: P(α•u + w) = α•P(u) + P(w) = α•u + 0 = α•u
  rw [map_add, map_smul, projLine_apply_self (𝕜 := 𝕜) u hu]
  -- P(w) = ⟪u,w⟫ • u = 0 • u = 0 since w ⊥ u
  rw [projLine_apply, hw, zero_smul, add_zero, add_sub_cancel_left]

end props

end RankOneToggle