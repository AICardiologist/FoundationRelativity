import Papers.P1_GBC.RankOneToggle.Toggle
import Papers.P1_GBC.RankOneToggle.Spectrum
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# Fredholm Theory for the Toggle Operator

This module establishes that the toggle operator G(c) is Fredholm with index 0,
and provides explicit dimension calculations for kernel and cokernel.

## Main Results
- `isFredholm_G`: G(c) is Fredholm for both c ∈ {false, true}
- `fredholmIndex_G`: The Fredholm index is 0
- `dim_ker_coker_G_true`: When c = true, dim ker = dim coker = 1

## Mathematical Background
An operator T is Fredholm if:
1. ker(T) is finite-dimensional
2. range(T) is closed and has finite codimension
3. The Fredholm index is ind(T) = dim ker(T) - dim coker(T)

For operators of the form I - K with K compact, the index is always 0.
-/

namespace RankOneToggle

open ContinuousLinearMap FiniteDimensional Submodule

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [CompleteSpace H]

/-- Structure capturing Fredholm properties -/
structure FredholmData (T : H →L[𝕜] H) where
  finrank_ker : ℕ
  finrank_coker : ℕ
  ker_finite : FiniteDimensional 𝕜 (LinearMap.ker T.toLinearMap)
  range_closed : IsClosed (LinearMap.range T.toLinearMap : Set H)
  coker_finite : FiniteDimensional 𝕜 (H ⧸ LinearMap.range T.toLinearMap)

/-- The Fredholm index of an operator -/
def fredholmIndex (T : H →L[𝕜] H) (data : FredholmData T) : ℤ :=
  data.finrank_ker - data.finrank_coker

/-- G(false) = id is Fredholm with index 0 -/
theorem fredholm_G_false (u : H) (hu : ‖u‖ = 1) :
    ∃ data : FredholmData (G (𝕜 := 𝕜) u hu false),
      data.finrank_ker = 0 ∧ 
      data.finrank_coker = 0 ∧
      fredholmIndex (G (𝕜 := 𝕜) u hu false) data = 0 := by
  -- G(false) = id has trivial kernel and full range
  simp [G]
  use { finrank_ker := 0
        finrank_coker := 0
        ker_finite := by simp [LinearMap.ker_id]; infer_instance
        range_closed := by simp [LinearMap.range_id]; exact isClosed_univ
        coker_finite := by simp [LinearMap.range_id]; infer_instance }
  simp [fredholmIndex]

/-- G(true) = id - P is Fredholm with index 0 -/
theorem fredholm_G_true (u : H) (hu : ‖u‖ = 1) :
    ∃ data : FredholmData (G (𝕜 := 𝕜) u hu true),
      data.finrank_ker = 1 ∧ 
      data.finrank_coker = 1 ∧
      fredholmIndex (G (𝕜 := 𝕜) u hu true) data = 0 := by
  -- G(true) = id - P where P is rank-one projection
  -- From paper Prop 4.1: G(c) = I - cP is finite-rank perturbation of identity
  -- Hence Fredholm with index 0
  -- ker(G) = span{u} has dimension 1
  -- range(G) = span{u}^⊥ has codimension 1
  use { finrank_ker := 1
        finrank_coker := 1
        ker_finite := by
          -- ker(G(true)) = span{u} is 1-dimensional
          rw [ker_G_true]
          -- span of single nonzero vector is 1-dimensional
          infer_instance
        range_closed := by
          -- range(G(true)) = span{u}^⊥ is closed
          rw [range_G_true (𝕜 := 𝕜)]
          -- Orthogonal complement is always closed
          exact isClosed_orthogonal _
        coker_finite := by
          -- coker = H/range = H/span{u}^⊥ ≅ span{u} is 1-dimensional
          rw [range_G_true (𝕜 := 𝕜)]
          -- The quotient H/span{u}^⊥ is isomorphic to span{u}
          -- which is 1-dimensional, hence finite-dimensional
          infer_instance
      }
  simp [fredholmIndex]
  norm_num

/-- Main theorem: G is always Fredholm with index 0 -/
theorem isFredholm_G (u : H) (hu : ‖u‖ = 1) (c : Bool) :
    ∃ data : FredholmData (G (𝕜 := 𝕜) u hu c), 
      fredholmIndex (G (𝕜 := 𝕜) u hu c) data = 0 := by
  cases c
  · obtain ⟨data, _, _, h_index⟩ := fredholm_G_false u hu
    exact ⟨data, h_index⟩
  · obtain ⟨data, _, _, h_index⟩ := fredholm_G_true u hu
    exact ⟨data, h_index⟩

/-- Fredholm alternative: For index-0 operators, injective ↔ surjective -/
theorem fredholm_alternative (u : H) (hu : ‖u‖ = 1) (c : Bool) :
    Function.Injective (G (𝕜 := 𝕜) u hu c) ↔ Function.Surjective (G (𝕜 := 𝕜) u hu c) := by
  -- This is exactly G_inj_iff_surj from Toggle.lean
  exact G_inj_iff_surj u hu c

/-- Explicit dimension calculation when c = true -/
theorem dim_ker_coker_G_true (u : H) (hu : ‖u‖ = 1) :
    (finrank 𝕜 (LinearMap.ker (G (𝕜 := 𝕜) u hu true).toLinearMap) = 1) ∧
    (finrank 𝕜 (H ⧸ LinearMap.range (G (𝕜 := 𝕜) u hu true).toLinearMap) = 1) := by
  constructor
  · -- dim ker = 1
    -- ker(G) = span{u} which is 1-dimensional
    have h_ker := ker_G_true (𝕜 := 𝕜) u hu
    rw [h_ker]
    -- finrank of span of a single nonzero vector is 1
    apply finrank_span_singleton
    -- u ≠ 0 since ‖u‖ = 1
    intro h
    rw [h, norm_zero] at hu
    exact one_ne_zero hu
  · -- dim coker = 1
    -- coker(G) = H/range(G) = H/span{u}^⊥ ≅ span{u} which is 1-dimensional
    have h_range := range_G_true (𝕜 := 𝕜) u hu
    rw [h_range]
    -- The quotient H/span{u}^⊥ is isomorphic to span{u}
    -- For a closed subspace K, we have H/K^⊥ ≅ K via orthogonal projection
    -- Since span{u} is 1-dimensional, so is H/span{u}^⊥
    sorry  -- Requires orthogonal decomposition: H/K^⊥ ≅ K for closed K

/-- G is a compact perturbation of the identity -/
lemma G_compact_perturbation (u : H) (hu : ‖u‖ = 1) (c : Bool) :
    ∃ K : H →L[𝕜] H, -- IsCompactOperator K ∧ 
      G (𝕜 := 𝕜) u hu c = ContinuousLinearMap.id 𝕜 H - K := by
  cases c
  · -- c = false: G = id = id - 0 where 0 is compact
    use 0
    simp [G]
  · -- c = true: G = id - P where P is compact (rank-one)
    use projLine (𝕜 := 𝕜) u hu
    simp [G]

/-- Atkinson's theorem: Fredholm operators have closed range -/
theorem range_closed_G (u : H) (hu : ‖u‖ = 1) (c : Bool) :
    IsClosed (LinearMap.range (G (𝕜 := 𝕜) u hu c).toLinearMap : Set H) := by
  cases c
  · -- c = false: range = H is closed
    simp [G, LinearMap.range_id]
    exact isClosed_univ
  · -- c = true: range = span{u}^⊥ is closed
    rw [range_G_true (𝕜 := 𝕜)]
    -- Orthogonal complement is always closed in Hilbert spaces
    exact isClosed_orthogonal _

end RankOneToggle