import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

noncomputable section
open scoped ComplexConjugate

namespace RankOneToggle

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Orthogonal projection onto the line spanned by a unit vector `u`. -/
def projLine (u : H) (hu : ‖u‖ = 1) : H →L[𝕜] H :=
  LinearMap.mkContinuous
    { toFun    := fun x => (@inner 𝕜 H _ u x) • u
      map_add' := by
        intro x y
        simpa [inner_add_right, add_smul]
      map_smul' := by
        intro c x
        simpa [inner_smul_right, smul_smul] }
    1
    (by
      intro x
      have h₀ : ‖@inner 𝕜 H _ u x‖ ≤ ‖u‖ * ‖x‖ := norm_inner_le_norm u x
      have h₁ : ‖@inner 𝕜 H _ u x‖ ≤ ‖x‖ := by simpa [hu, one_mul] using h₀
      calc
        ‖(@inner 𝕜 H _ u x) • u‖ = ‖@inner 𝕜 H _ u x‖ * ‖u‖ := norm_smul _ _
        _                 = ‖@inner 𝕜 H _ u x‖       := by simpa [hu]
        _                 ≤ ‖x‖               := h₁
        _                 ≤ (1 : ℝ) * ‖x‖     := by simpa)

/-- Pointwise formula for the projection. -/
@[simp] lemma projLine_apply (u : H) (hu : ‖u‖ = 1) (x : H) :
    projLine u hu x = (@inner 𝕜 H _ u x) • u := rfl

/-- Idempotence: `(projLine u hu) ∘ (projLine u hu) = projLine u hu`. -/
lemma projLine_idem (u : H) (hu : ‖u‖ = 1) :
    (projLine u hu).comp (projLine u hu) = projLine u hu := by
  ext x
  have hself : @inner 𝕜 H _ u u = (‖u‖ : ℝ) ^ 2 := inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) u
  -- Expand and simplify using linearity in the second argument and ‖u‖ = 1
  simp only [projLine_apply, ContinuousLinearMap.comp_apply, inner_smul_right, hself]
  norm_num [hu]

/-- `projLine u hu u = u`. -/
@[simp] lemma projLine_apply_self (u : H) (hu : ‖u‖ = 1) :
    projLine u hu u = u := by
  have hself : @inner 𝕜 H _ u u = (‖u‖ : ℝ) ^ 2 := inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) u
  simp only [projLine_apply, hself]
  norm_num [hu]

/-- `range (projLine u hu) = span {u}`. -/
lemma range_projLine (u : H) (hu : ‖u‖ = 1) :
    LinearMap.range (projLine u hu).toLinearMap = Submodule.span 𝕜 ({u} : Set H) := by
  ext x
  constructor
  · -- Every image is a scalar multiple of `u`.
    rintro ⟨y, rfl⟩
    simpa [projLine_apply] using
      Submodule.smul_mem (Submodule.span 𝕜 ({u} : Set H)) (@inner 𝕜 H _ u y)
        (Submodule.subset_span (by simp))
  · -- Conversely, any `c • u` is hit by `x := c • u`.
    intro hx
    rcases Submodule.mem_span_singleton.mp hx with ⟨c, rfl⟩
    refine ⟨c • u, ?_⟩
    have hself : @inner 𝕜 H _ u u = (‖u‖ : ℝ) ^ 2 := inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) u
    simp only [projLine_apply, inner_smul_right, hself]
    norm_num [hu]

end RankOneToggle