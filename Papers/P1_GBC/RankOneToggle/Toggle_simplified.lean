import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Rank-One Toggle Operator (Simplified Version)

This module defines the rank-one toggle operator G(c) := id - c·P where c ∈ {false, true}
and P is a rank-one projection onto a line in a Hilbert space.

This simplified version works around Lean 4 typeclass resolution issues by avoiding
complex definitions and focusing on the essential mathematics.
-/

namespace RankOneToggle

open ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The projection function onto the line spanned by u (unbundled). -/
def projFn (u : H) (x : H) : H := (@inner 𝕜 _ _ u x) • u

/-- Rank-one toggle function G(c) := id - (if c then 1 else 0) • P. -/
def GFn (u : H) (c : Bool) (x : H) : H :=
  x - (if c then (1 : 𝕜) else 0) • projFn u x

lemma GFn_false (u : H) (x : H) :
    GFn u false x = x := by
  simp [GFn, projFn]

lemma GFn_true (u : H) (x : H) :
    GFn u true x = x - projFn u x := by
  simp [GFn, projFn]

/-- When c = true and u is a unit vector, the kernel of G is span{u} -/
lemma ker_GFn_true (u : H) (hu : ‖u‖ = 1) :
    {x : H | GFn u true x = 0} = {x : H | ∃ c : 𝕜, x = c • u} := by
  ext x
  simp only [Set.mem_setOf_eq, GFn_true, projFn]
  constructor
  · intro h
    -- If x - ⟪u, x⟫ • u = 0, then x = ⟪u, x⟫ • u
    rw [sub_eq_zero] at h
    exact ⟨@inner 𝕜 _ _ u x, h.symm⟩
  · rintro ⟨c, rfl⟩
    -- If x = c • u, then x - ⟪u, x⟫ • u = 0
    simp [inner_smul_right, inner_self_eq_norm_sq_to_K, hu]
    ring

/-- When c = true and u is a unit vector, the range of G is the orthogonal complement of span{u} -/
lemma range_GFn_true (u : H) (hu : ‖u‖ = 1) :
    {GFn u true x | x : H} = {y : H | @inner 𝕜 _ _ u y = 0} := by
  ext y
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    -- G(x) = x - ⟪u, x⟫ • u is orthogonal to u
    simp only [GFn_true, projFn]
    rw [inner_sub_right, inner_smul_right]
    simp [inner_self_eq_norm_sq_to_K, hu]
    ring
  · intro hy
    -- If y ⊥ u, then y = G(y) since ⟪u, y⟫ = 0
    use y
    simp only [GFn_true, projFn, hy]
    simp

/-- When c = false, the kernel is trivial -/
lemma ker_GFn_false (u : H) :
    {x : H | GFn u false x = 0} = {0} := by
  ext x
  simp [GFn_false]

/-- When c = false, the range is the whole space -/
lemma range_GFn_false (u : H) :
    {GFn u false x | x : H} = Set.univ := by
  ext y
  simp [GFn_false]
  use y

/-- G is injective if and only if c = false -/
theorem injective_GFn_iff (u : H) (hu : ‖u‖ = 1) (c : Bool) :
    Function.Injective (GFn u c) ↔ c = false := by
  constructor
  · intro h
    -- If G is injective, then ker(G) = {0}
    cases c
    · rfl
    · -- c = true case: ker(G) = span{u} ≠ {0}, contradiction
      exfalso
      have h_ker := ker_GFn_true u hu
      have : GFn u true u = 0 := by
        simp [GFn_true, projFn]
        rw [inner_self_eq_norm_sq_to_K, hu]
        simp
      have hu_ne : u ≠ 0 := by
        intro h_eq
        rw [h_eq, norm_zero] at hu
        exact one_ne_zero hu
      have : GFn u true u = GFn u true 0 := by simp [this, GFn_true, projFn]
      exact hu_ne (h this)
  · intro h
    rw [h]
    intro x y hxy
    simp [GFn_false] at hxy
    exact hxy

/-- G is surjective if and only if c = false -/
theorem surjective_GFn_iff (u : H) (hu : ‖u‖ = 1) (c : Bool) :
    Function.Surjective (GFn u c) ↔ c = false := by
  constructor
  · intro h
    cases c
    · rfl
    · -- c = true case: range(G) = span{u}^⊥ ≠ H, contradiction
      exfalso
      have h_range := range_GFn_true u hu
      -- u is not in the range of G when c = true
      have hu_not_in_range : u ∉ {GFn u true x | x : H} := by
        rw [h_range]
        simp only [Set.mem_setOf_eq]
        rw [inner_self_eq_norm_sq_to_K, hu]
        simp
        exact one_ne_zero
      obtain ⟨x, hx⟩ := h u
      exact hu_not_in_range ⟨x, hx⟩
  · intro h
    rw [h]
    intro y
    use y
    exact GFn_false u y

/-- Fredholm alternative: For the toggle operator, injectivity ↔ surjectivity -/
theorem GFn_inj_iff_surj (u : H) (hu : ‖u‖ = 1) (c : Bool) :
    Function.Injective (GFn u c) ↔ Function.Surjective (GFn u c) := by
  rw [injective_GFn_iff, surjective_GFn_iff]

/-- G² = G when c = true (idempotent complementary projection) -/
lemma GFn_true_idem (u : H) (hu : ‖u‖ = 1) (x : H) :
    GFn u true (GFn u true x) = GFn u true x := by
  simp only [GFn_true, projFn]
  -- Calculate: (x - ⟪u, x⟫ • u) - ⟪u, x - ⟪u, x⟫ • u⟫ • u
  rw [inner_sub_right, inner_smul_right]
  simp [inner_self_eq_norm_sq_to_K, hu]
  ring

end RankOneToggle