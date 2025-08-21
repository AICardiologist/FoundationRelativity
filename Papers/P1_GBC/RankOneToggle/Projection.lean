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
  let f : H →ₗ[𝕜] H := {
    toFun    := fun x => ⟪u, x⟫_𝕜 • u,
    map_add' := by
      intro x y
      simp [inner_add_right, add_smul],
    map_smul' := by
      intro c x
      simp [inner_smul_right, smul_smul]
  }
  f.mkContinuous 1 (by
    intro x
    have h : ‖⟪u, x⟫_𝕜‖ ≤ ‖x‖ := by
      have := norm_inner_le_norm u x
      simpa [hu, one_mul] using this
    calc
      ‖f x‖ = ‖⟪u, x⟫_𝕜 • u‖ := rfl
      _     = ‖⟪u, x⟫_𝕜‖ * ‖u‖ := norm_smul _ _
      _     = ‖⟪u, x⟫_𝕜‖       := by rw [hu, mul_one]
      _     ≤ ‖x‖               := h
      _     ≤ (1 : ℝ) * ‖x‖     := by rw [one_mul])

@[simp] lemma projLine_apply (u : H) (hu : ‖u‖ = 1) (x : H) :
  projLine u hu x = ⟪u, x⟫_𝕜 • u := rfl

/-- Idempotence. -/
lemma projLine_idem (u : H) (hu : ‖u‖ = 1) :
  (projLine u hu).comp (projLine u hu) = projLine u hu := by
  ext x
  simp [projLine_apply, inner_smul_right, inner_self_eq_norm_sq_to_K, hu, smul_smul]

@[simp] lemma projLine_apply_self (u : H) (hu : ‖u‖ = 1) :
  projLine u hu u = u := by
  simp [projLine_apply, inner_self_eq_norm_sq_to_K, hu]

lemma range_projLine (u : H) (hu : ‖u‖ = 1) :
  LinearMap.range (projLine u hu).toLinearMap = Submodule.span 𝕜 {u} := by
  ext x
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  constructor
  · rintro ⟨y, rfl⟩
    rw [projLine_apply]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  · intro hx
    rcases Submodule.mem_span_singleton.mp hx with ⟨c, rfl⟩
    use c • u
    simp [projLine_apply, inner_smul_right, inner_self_eq_norm_sq_to_K, hu]

-- For now, comment out the kernel lemma until we can fix the proof
-- lemma ker_projLine (u : H) (hu : ‖u‖ = 1) :
--   LinearMap.ker (projLine u hu).toLinearMap = (Submodule.span 𝕜 {u})ᗮ := by
--   sorry

end RankOneToggle