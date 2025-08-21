import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

noncomputable section
open scoped ComplexConjugate

namespace RankOneToggle

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Orthogonal projection onto the line spanned by a unit vector `u`. -/
def projLine (u : H) (hu : ‖u‖ = 1) : H →L[𝕜] H := by
  -- 1) Build a plain linear map with the required fields.
  let f : H →ₗ[𝕜] H :=
  { toFun    := fun x => ⟪u, x⟫_𝕜 • u,
    map_add' := by
      intro x y
      simp [inner_add_right, add_smul],
    map_smul' := by
      intro c x
      simp [inner_smul_right, smul_smul] }
  -- 2) Prove a global bound and upgrade it to a continuous linear map.
  refine f.mkContinuous 1 (by
    intro x
    have h : ‖⟪u, x⟫_𝕜‖ ≤ ‖x‖ := by
      -- Cauchy–Schwarz: ‖⟪u,x⟫‖ ≤ ‖u‖‖x‖ and ‖u‖ = 1
      have := norm_inner_le_norm u x
      simpa [hu, one_mul] using this
    calc
      ‖f x‖ = ‖⟪u, x⟫_𝕜 • u‖ := rfl
      _     = ‖⟪u, x⟫_𝕜‖ * ‖u‖ := by simpa using norm_smul (⟪u, x⟫_𝕜) u
      _     = ‖⟪u, x⟫_𝕜‖       := by simpa [hu]
      _     ≤ ‖x‖               := h
      _     ≤ (1 : ℝ) * ‖x‖     := by simpa)

@[simp] lemma projLine_apply (u : H) (hu : ‖u‖ = 1) (x : H) :
  projLine u hu x = ⟪u, x⟫_𝕜 • u := rfl

/-- Idempotence: `P ∘ P = P`. -/
lemma projLine_idem (u : H) (hu : ‖u‖ = 1) :
  (projLine u hu).comp (projLine u hu) = projLine u hu := by
  ext x
  simp [projLine_apply, inner_smul_right, inner_self_eq_norm_sq_to_K, hu, smul_smul]

/-- `P(u) = u`. -/
@[simp] lemma projLine_apply_self (u : H) (hu : ‖u‖ = 1) :
  projLine u hu u = u := by
  simp [projLine_apply, inner_self_eq_norm_sq_to_K, hu]

/-- `range P = span {u}`. -/
lemma range_projLine (u : H) (hu : ‖u‖ = 1) :
  LinearMap.range (projLine u hu).toLinearMap = Submodule.span 𝕜 {u} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simpa [projLine_apply] using
      Submodule.smul_mem (Submodule.span 𝕜 {u}) ⟪u, y⟫_𝕜
        (Submodule.subset_span (by simp))
  · intro hx
    rcases Submodule.mem_span_singleton.mp hx with ⟨c, rfl⟩
    refine ⟨c • u, ?_⟩
    simp [projLine_apply, inner_smul_right, inner_self_eq_norm_sq_to_K, hu, smul_smul]

/-- `ker P = (span {u})ᗮ`. -/
lemma ker_projLine (u : H) (hu : ‖u‖ = 1) :
  LinearMap.ker (projLine u hu).toLinearMap = (Submodule.span 𝕜 {u})ᗮ := by
  ext x
  constructor
  · intro hx
    have : ⟪u, x⟫_𝕜 = 0 := by
      have := congrArg (fun z : H => ⟪u, z⟫_𝕜) hx
      simpa [projLine_apply, inner_smul_left, inner_self_eq_norm_sq_to_K, hu] using this
    simpa [Submodule.mem_orthogonal_singleton_iff_inner_left, this]
  · intro hx
    have : ⟪u, x⟫_𝕜 = 0 := by
      simpa [Submodule.mem_orthogonal_singleton_iff_inner_left] using hx
    simp [LinearMap.mem_ker, projLine_apply, this]

end RankOneToggle