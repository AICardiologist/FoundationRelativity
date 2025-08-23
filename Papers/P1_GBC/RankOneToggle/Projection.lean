import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

noncomputable section

namespace RankOneToggle

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The projection function onto the line spanned by u (unbundled). -/
def projFn (u : H) (x : H) : H := (@inner 𝕜 _ _ u x) • u

/-- Orthogonal projection onto the line spanned by a unit vector `u`. -/
def projLine (u : H) (hu : ‖u‖ = 1) : H →L[𝕜] H := 
  LinearMap.mkContinuous
    { toFun := projFn u
      map_add' := fun x y => by simp [projFn, inner_add_right, add_smul]
      map_smul' := fun c x => by 
        simp only [projFn, RingHom.id_apply]
        show @inner 𝕜 _ _ u (c • x) • u = c • (@inner 𝕜 _ _ u x • u)
        rw [@inner_smul_right 𝕜 H, mul_smul] }
    1
    (fun x => by
      have h₀ : ‖@inner 𝕜 _ _ u x‖ ≤ ‖u‖ * ‖x‖ := norm_inner_le_norm u x
      have h₁ : ‖@inner 𝕜 _ _ u x‖ ≤ ‖x‖ := by rw [hu, one_mul] at h₀; exact h₀
      calc ‖projFn u x‖ = ‖(@inner 𝕜 _ _ u x) • u‖ := rfl
        _ = ‖@inner 𝕜 _ _ u x‖ * ‖u‖ := norm_smul _ _
        _ = ‖@inner 𝕜 _ _ u x‖ := by rw [hu, mul_one]
        _ ≤ ‖x‖ := h₁
        _ ≤ 1 * ‖x‖ := by rw [one_mul])

section lemmas
variable {𝕜 H : Type*}
variable [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

@[simp] lemma projLine_apply (u : H) (hu : ‖u‖ = 1) (x : H) :
  projLine (𝕜 := 𝕜) u hu x = (inner (𝕜 := 𝕜) u x) • u := rfl

@[simp] lemma inner_projLine_left (u : H) (hu : ‖u‖ = 1) (x : H) :
  inner (𝕜 := 𝕜) u (projLine (𝕜 := 𝕜) u hu x) = inner (𝕜 := 𝕜) u x := by
  -- ⟪u, ⟪u,x⟫ • u⟫ = ⟪u,x⟫ * ⟪u,u⟫ = ⟪u,x⟫
  simp [projLine_apply, inner_smul_right, inner_self_eq_norm_sq_to_K, hu]

lemma projLine_idem (u : H) (hu : ‖u‖ = 1) :
  (projLine (𝕜 := 𝕜) u hu).comp (projLine (𝕜 := 𝕜) u hu) = projLine (𝕜 := 𝕜) u hu := by
  ext x
  -- (P ∘ P) x = P x
  simp [ContinuousLinearMap.comp_apply, projLine_apply, inner_self_eq_norm_sq_to_K, hu]

@[simp] lemma projLine_apply_self (u : H) (hu : ‖u‖ = 1) :
  projLine (𝕜 := 𝕜) u hu u = u := by
  simp [projLine_apply, inner_self_eq_norm_sq_to_K, hu]

lemma range_projLine (u : H) (hu : ‖u‖ = 1) :
  LinearMap.range (projLine (𝕜 := 𝕜) u hu).toLinearMap = Submodule.span 𝕜 {u} := by
  ext x
  constructor
  · -- every image is of the form ⟪u,y⟫ • u
    rintro ⟨y, rfl⟩
    simp only [ContinuousLinearMap.coe_coe, projLine_apply]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  · -- conversely, any c • u is in the range (hit by y := c • u)
    intro hx
    rcases Submodule.mem_span_singleton.mp hx with ⟨c, rfl⟩
    refine ⟨c • u, ?_⟩
    -- P (c • u) = c • u
    simp only [ContinuousLinearMap.coe_coe, projLine_apply, inner_smul_right, inner_self_eq_norm_sq_to_K, hu]
    simp

/-! ## Operator Norm Analysis

**Mathematical Fact**: The operator norm of projLine is 1 for unit vectors u.

**Proof outline**: ‖P‖ = sup{‖Px‖ : ‖x‖≤1} = sup{|⟪u,x⟫| : ‖x‖≤1} 
By Cauchy-Schwarz: |⟪u,x⟫| ≤ ‖u‖‖x‖ ≤ 1, with equality at x = u.
Hence ‖P‖ = 1.

**Implementation Status**: This requires operator norm API not available in the pinned mathlib.
The mathematical content builds on the continuity bound (≤ 1) proven in the definition above.
-/
end lemmas

end RankOneToggle