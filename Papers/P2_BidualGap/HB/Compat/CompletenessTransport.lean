/-
  CompletenessTransport: transfer CompleteSpace across (uniform) equivalences.
  This removes sensitivity to mathlib API names/locations for completeness transport.
-/
import Mathlib.Topology.Algebra.Module
import Mathlib.Topology.Algebra.UniformGroup
import Mathlib.Topology.UniformSpace.Basic

noncomputable section
open Filter Topology

namespace Papers.P2_BidualGap.HB.Compat

/-- If `e : X ≃ Y` is a *uniform* equivalence (both directions uniformly continuous),
    completeness transfers from `X` to `Y`. -/
theorem completeSpace_of_uniformEquiv
  {X Y : Type*} [UniformSpace X] [UniformSpace Y]
  (e : X ≃ Y)
  (h₁ : UniformContinuous e)
  (h₂ : UniformContinuous e.symm) :
  CompleteSpace X → CompleteSpace Y := by
  intro hX
  refine ⟨?_⟩
  intro F hF
  -- Pull the Cauchy filter on Y back to X via e.symm, which is uniformly continuous.
  let G : Filter X := Filter.map e.symm F
  have hG : Cauchy G := hF.map h₂
  -- Use completeness of X to get a limit point.
  rcases (show CompleteSpace X from hX) with ⟨hcomp⟩
  rcases hcomp hG with ⟨x, hx⟩
  -- Push forward the convergence back along e.
  have hmap_mono : Filter.map e G ≤ Filter.map e (𝓝 x) := Filter.map_mono hx
  have hcont : Filter.map e (𝓝 x) ≤ 𝓝 (e x) := (h₁.continuous.tendsto x)
  -- `F = map e (map e.symm F)` since e ∘ e.symm = id.
  have hEq : F = Filter.map e G := by
    dsimp [G]
    simpa [Filter.map_map, Function.comp, e.right_inv]
  exact ⟨e x, by simpa [hEq] using hmap_mono.trans hcont⟩

/-- Specialization: transport completeness across a linear isometry equivalence. -/
theorem completeSpace_of_linearIsometryEquiv
  {𝕜 : Type*} [IsROrC 𝕜]
  {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (e : E ≃ₗᵢ[𝕜] F) :
  CompleteSpace E → CompleteSpace F := by
  -- A linear isometry (and its inverse) are uniformly continuous.
  have h₁ : UniformContinuous e := e.isometry.uniformContinuous
  have h₂ : UniformContinuous e.symm := e.symm.isometry.uniformContinuous
  simpa using completeSpace_of_uniformEquiv e.toEquiv h₁ h₂

/-- Equivalence of completeness across a linear isometry equivalence. -/
theorem completeSpace_iff_of_linearIsometryEquiv
  {𝕜 : Type*} [IsROrC 𝕜]
  {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (e : E ≃ₗᵢ[𝕜] F) :
  CompleteSpace E ↔ CompleteSpace F := by
  constructor
  · intro hE; exact completeSpace_of_linearIsometryEquiv (E:=E) (F:=F) e hE
  · intro hF; have := completeSpace_of_linearIsometryEquiv (E:=F) (F:=E) e.symm hF; simpa using this

end Papers.P2_BidualGap.HB.Compat