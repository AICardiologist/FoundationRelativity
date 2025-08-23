/-
  FredholmAlt.lean
  Lightweight "index-zero" specification for the rank-one toggle G(true) = Id - P,
  avoiding finrank/quotient APIs that are unavailable in the pinned mathlib.
-/
import Papers.P1_GBC.RankOneToggle.Toggle
open scoped InnerProductSpace
open ContinuousLinearMap

namespace RankOneToggle

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- A lightweight "index-zero" specification that avoids dimension numerics.
    It records that the kernel and the range look exactly like a 1D line and its
    orthogonal complement. This is the algebra-free content we can prove now. -/
structure IndexZeroSpec (T : H →L[𝕜] H) : Prop where
  exists_unit_vector :
    ∃ (u : H) (_hu : ‖u‖ = 1),
        LinearMap.ker T.toLinearMap   = Submodule.span 𝕜 ({u} : Set H)
      ∧ LinearMap.range T.toLinearMap = (Submodule.span 𝕜 ({u} : Set H)).orthogonal

namespace IndexZeroSpec

/-- For the toggle `G true`, the lightweight index-zero spec holds immediately from
    the kernel/range theorems in `Toggle.lean`. -/
theorem of_toggle_true (u : H) (hu : ‖u‖ = 1) :
    IndexZeroSpec (G (𝕜 := 𝕜) u hu true) := by
  refine ⟨?w⟩
  refine ⟨u, hu, ?_, ?_⟩
  · -- kernel equality from Toggle.lean
    simpa using (ker_G_true (𝕜 := 𝕜) (u := u) (hu := hu))
  · -- range equality from Toggle.lean
    simpa using (range_G_true (𝕜 := 𝕜) (u := u) (hu := hu))

end IndexZeroSpec

/-- Convenience wrapper. -/
theorem indexZeroSpec_toggle_true (u : H) (hu : ‖u‖ = 1) :
    IndexZeroSpec (G (𝕜 := 𝕜) u hu true) :=
  IndexZeroSpec.of_toggle_true (𝕜 := 𝕜) u hu

end RankOneToggle