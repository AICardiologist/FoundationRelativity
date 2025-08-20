import Papers.P1_GBC.RankOneToggle.Projection

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
  ContinuousLinearMap.id 𝕜 H - (if c then (1 : 𝕜) else 0) • projLine u hu

@[simp]
lemma G_false (u : H) (hu : ‖u‖ = 1) :
    G u hu false = ContinuousLinearMap.id 𝕜 H := by
  simp [G]

@[simp]
lemma G_true (u : H) (hu : ‖u‖ = 1) :
    G u hu true = ContinuousLinearMap.id 𝕜 H - projLine u hu := by
  simp [G]

lemma G_apply (u : H) (hu : ‖u‖ = 1) (c : Bool) (x : H) :
    G u hu c x = x - (if c then (1 : 𝕜) else 0) • projLine u hu x := by
  simp [G]

/-- When c = true, the kernel of G is span{u} -/
lemma ker_G_true (u : H) (hu : ‖u‖ = 1) :
    LinearMap.ker (G u hu true).toLinearMap = Submodule.span 𝕜 {u} := by
  ext x
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, G_true,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  constructor
  · intro h
    -- If x - P(x) = 0, then x = P(x), so x ∈ range(P) = span{u}
    rw [sub_eq_zero] at h
    rw [← h]
    have := range_projLine u hu
    rw [← this]
    exact ⟨x, rfl⟩
  · intro hx
    -- If x ∈ span{u}, then P(x) = x, so x - P(x) = 0
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    simp [projLine_apply, inner_smul_right, smul_assoc]
    rw [inner_self_eq_norm_sq_to_K, hu, one_pow, RCLike.one_re]
    simp

/-- When c = true, the range of G is the orthogonal complement of span{u} -/
lemma range_G_true (u : H) (hu : ‖u‖ = 1) :
    LinearMap.range (G u hu true).toLinearMap = (Submodule.span 𝕜 {u})ᗮ := by
  ext x
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  constructor
  · rintro ⟨y, rfl⟩
    -- G(y) = y - P(y) is orthogonal to u
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    simp only [G_true, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    rw [inner_sub_right, projLine_apply]
    simp [inner_self_eq_norm_sq_to_K, hu, RCLike.one_re]
  · intro hx
    -- If x ⊥ u, then x = G(x) since P(x) = 0
    use x
    simp only [G_true, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at hx
    simp [projLine_apply, hx]

/-- When c = false, the kernel is trivial -/
lemma ker_G_false (u : H) (hu : ‖u‖ = 1) :
    LinearMap.ker (G u hu false).toLinearMap = ⊥ := by
  simp [G_false, LinearMap.ker_id]

/-- When c = false, the range is the whole space -/
lemma range_G_false (u : H) (hu : ‖u‖ = 1) :
    LinearMap.range (G u hu false).toLinearMap = ⊤ := by
  simp [G_false, LinearMap.range_id]

/-- G is injective if and only if c = false -/
theorem injective_iff (u : H) (hu : ‖u‖ = 1) (c : Bool) :
    Function.Injective (G u hu c) ↔ c = false := by
  constructor
  · intro h
    -- If G is injective, then ker(G) = {0}
    cases c
    · rfl
    · -- c = true case: ker(G) = span{u} ≠ {0}, contradiction
      exfalso
      have h_ker := ker_G_true u hu
      have : u ∈ LinearMap.ker (G u hu true).toLinearMap := by
        rw [h_ker]
        exact Submodule.mem_span_singleton_self u
      rw [LinearMap.mem_ker] at this
      have hu_ne : u ≠ 0 := by
        intro h_eq
        rw [h_eq, norm_zero] at hu
        exact one_ne_zero hu
      exact hu_ne (h this)
  · intro h
    rw [h]
    simp [G_false]
    exact Function.injective_id

/-- G is surjective if and only if c = false -/
theorem surjective_iff (u : H) (hu : ‖u‖ = 1) (c : Bool) :
    Function.Surjective (G u hu c) ↔ c = false := by
  constructor
  · intro h
    cases c
    · rfl
    · -- c = true case: range(G) = span{u}^⊥ ≠ H (for nontrivial H), contradiction
      exfalso
      have h_range := range_G_true u hu
      -- u is not in the range of G when c = true
      have hu_not_in_range : u ∉ LinearMap.range (G u hu true).toLinearMap := by
        rw [h_range, Submodule.mem_orthogonal_singleton_iff_inner_left]
        rw [inner_self_eq_norm_sq_to_K, hu, one_pow, RCLike.one_re]
        exact one_ne_zero
      exact hu_not_in_range (LinearMap.mem_range_self _ u)
  · intro h
    rw [h]
    simp [G_false]
    exact Function.surjective_id

/-- Fredholm alternative: For the toggle operator, injectivity ↔ surjectivity -/
theorem G_inj_iff_surj (u : H) (hu : ‖u‖ = 1) (c : Bool) :
    Function.Injective (G u hu c) ↔ Function.Surjective (G u hu c) := by
  rw [injective_iff, surjective_iff]

/-- G² = G when c = true (idempotent complementary projection) -/
lemma G_true_idem (u : H) (hu : ‖u‖ = 1) :
    (G u hu true).comp (G u hu true) = G u hu true := by
  ext x
  simp only [comp_apply, G_true, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  -- (id - P)(id - P) = id - 2P + P² = id - 2P + P = id - P
  rw [sub_sub, sub_add]
  congr 1
  rw [two_smul]
  congr 1
  exact projLine_idem u hu

/-- Block decomposition: H = ker(G) ⊕ range(G) when c = true -/
lemma block_decomposition_true (u : H) (hu : ‖u‖ = 1) [CompleteSpace H] :
    LinearMap.ker (G u hu true).toLinearMap ⊔ LinearMap.range (G u hu true).toLinearMap = ⊤ := by
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
    use ⟪u, x⟫_𝕜 • u, x - ⟪u, x⟫_𝕜 • u
    constructor
    · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    · constructor
      · -- Show x - ⟪u, x⟫ • u ∈ span{u}^⊥
        rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
        simp [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hu, RCLike.one_re]
      · -- Show x = ⟪u, x⟫ • u + (x - ⟪u, x⟫ • u)
        ring

end RankOneToggle