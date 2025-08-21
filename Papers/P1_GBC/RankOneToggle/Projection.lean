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
    { toFun    := fun x => @inner 𝕜 _ _ u x • u,
      map_add' := by
        intro x y
        -- `inner u (x + y) = inner u x + inner u y`
        -- and scalar multiplication distributes
        simpa [inner_add_right, add_smul],
      map_smul' := by
        intro c x
        -- `inner u (c • x) = c * inner u x` (linear in the second argument)
        -- and scalar multiplications compose
        simpa [inner_smul_right, smul_smul] }
    1
    (by
      intro x
      -- Cauchy–Schwarz: ‖⟪u,x⟫‖ ≤ ‖u‖‖x‖ and ‖u‖ = 1
      have h₀ : ‖@inner 𝕜 _ _ u x‖ ≤ ‖u‖ * ‖x‖ := norm_inner_le_norm u x
      have h₁ : ‖@inner 𝕜 _ _ u x‖ ≤ ‖x‖ := by simpa [hu, one_mul] using h₀
      calc
        ‖(@inner 𝕜 _ _ u x) • u‖ = ‖@inner 𝕜 _ _ u x‖ * ‖u‖ := norm_smul _ _
        _                 = ‖@inner 𝕜 _ _ u x‖       := by simpa [hu]
        _                 ≤ ‖x‖               := h₁
        _                 ≤ (1 : ℝ) * ‖x‖     := by simpa)

/-- Pointwise formula for the projection. -/
@[simp] lemma projLine_apply (u : H) (hu : ‖u‖ = 1) (x : H) :
    projLine u hu x = @inner 𝕜 _ _ u x • u := rfl

/-- Idempotence: `(projLine u hu) ∘ (projLine u hu) = projLine u hu`. -/
lemma projLine_idem (u : H) (hu : ‖u‖ = 1) :
    (projLine u hu).comp (projLine u hu) = projLine u hu := by
  ext x
  -- use linearity in the second coord and that ‖u‖=1
  simp only [projLine_apply, ContinuousLinearMap.comp_apply, inner_smul_right]
  rw [inner_self_eq_norm_sq_to_K, hu]
  simp

/-- `projLine u hu u = u`. -/
@[simp] lemma projLine_apply_self (u : H) (hu : ‖u‖ = 1) :
    projLine u hu u = u := by
  simp only [projLine_apply]
  rw [inner_self_eq_norm_sq_to_K, hu]
  simp

/-- `range (projLine u hu) = span {u}`. -/
lemma range_projLine (u : H) (hu : ‖u‖ = 1) :
    LinearMap.range (projLine u hu).toLinearMap = Submodule.span 𝕜 {u} := by
  ext x
  constructor
  · -- every image is a scalar multiple of `u`
    rintro ⟨y, rfl⟩
    simpa [projLine_apply] using
      Submodule.smul_mem (Submodule.span 𝕜 {u}) (@inner 𝕜 _ _ u y)
        (Submodule.subset_span (by simp))
  · -- conversely, any `c • u` is hit by `x := c • u`
    intro hx
    rcases Submodule.mem_span_singleton.mp hx with ⟨c, rfl⟩
    use c • u
    rw [projLine_apply]
    simp only [inner_smul_right, inner_self_eq_norm_sq_to_K]
    rw [hu]
    simp [smul_smul]

end RankOneToggle