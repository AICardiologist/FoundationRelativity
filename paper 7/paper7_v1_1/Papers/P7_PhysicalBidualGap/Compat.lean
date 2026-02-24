/-
Papers/P7_PhysicalBidualGap/Compat.lean
Utility: reflexivity transfer across linear isometric equivalences.

If X ≃ₗᵢ Y and Y is reflexive, then X is reflexive (and contrapositively,
if X is not reflexive, then Y is not reflexive).
-/
import Mathlib.Analysis.Normed.Module.Dual
import Papers.P7_PhysicalBidualGap.Basic

noncomputable section
namespace Papers.P7

open NormedSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- Reflexivity transfers across surjective linear isometries.
    If f : X →ₗᵢ Y is surjective (hence an isometric isomorphism)
    and Y is reflexive, then X is reflexive. -/
theorem reflexive_of_linearIsometryEquiv
    (e : X ≃ₗᵢ[𝕜] Y)
    (hY : IsReflexive 𝕜 Y) : IsReflexive 𝕜 X := by
  intro Φ -- Φ : X** (an element of the double dual of X)
  -- Construct dual map: e induces e* : Y* → X* via precomp
  -- For any g : Y*, (e*.g)(x) = g(e(x))
  let eL : X →L[𝕜] Y := e.toContinuousLinearEquiv.toContinuousLinearMap
  let eLs : Y →L[𝕜] X := e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let e_star : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X :=
    ContinuousLinearMap.precomp 𝕜 eL
  -- Transport Φ to Y** via e
  let Ψ : StrongDual 𝕜 (StrongDual 𝕜 Y) := Φ.comp e_star
  -- Since Y is reflexive, obtain y with J_Y(y) = Ψ
  obtain ⟨y, hy⟩ := hY Ψ
  -- Take x = e⁻¹(y)
  use e.symm y
  -- Need: J_X(e⁻¹(y)) = Φ, i.e., ∀ f : X*, f(e⁻¹(y)) = Φ(f)
  ext f
  -- Unfold J_X to get: f(e.symm y) = Φ(f)
  change f (e.symm y) = Φ f
  -- From hy: J_Y(y) = Ψ, so for g : Y*, g(y) = Ψ(g) = Φ(e_star g) = Φ(g ∘ eL)
  -- Take g = f ∘ eLs (= f ∘ e⁻¹)
  -- Then g(y) = f(eLs(y)) = f(e.symm y)  ← this is the LHS
  -- And Φ(e_star g) = Φ(g ∘ eL) = Φ(f ∘ eLs ∘ eL) = Φ(f ∘ id) = Φ(f)  ← RHS
  let g : StrongDual 𝕜 Y := f.comp eLs
  have h1 : g y = f (e.symm y) := by
    simp only [g, ContinuousLinearMap.comp_apply, eLs,
               ContinuousLinearEquiv.coe_coe,
               LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  have h2 : g y = Ψ g := by
    have := congr_fun (congr_arg DFunLike.coe hy) g
    simp only [inclusionInDoubleDual, ContinuousLinearMap.apply_apply] at this
    exact this
  have h3 : Ψ g = Φ f := by
    -- Ψ(g) = Φ(e_star(g)) = Φ(g ∘ eL)
    -- g ∘ eL = (f ∘ eLs) ∘ eL = f ∘ (eLs ∘ eL) = f ∘ id = f
    simp only [Ψ, ContinuousLinearMap.comp_apply]
    -- Need: Φ (e_star g) = Φ f, i.e., e_star g = f
    congr 1
    -- e_star g = g ∘ eL = (f ∘ eLs) ∘ eL
    ext x
    simp only [e_star, g, ContinuousLinearMap.precomp_apply,
               ContinuousLinearMap.comp_apply, eL, eLs,
               ContinuousLinearEquiv.coe_coe,
               LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    -- Need: f (e.symm (e x)) = f x
    simp [LinearIsometryEquiv.symm_apply_apply]
  rw [← h1, h2, h3]

/-- Contrapositive: if X is not reflexive and X ≃ₗᵢ Y, then Y is not reflexive. -/
theorem not_reflexive_of_linearIsometryEquiv
    (e : X ≃ₗᵢ[𝕜] Y)
    (hX : ¬ IsReflexive 𝕜 X) : ¬ IsReflexive 𝕜 Y :=
  fun hY => hX (reflexive_of_linearIsometryEquiv e hY)

end Papers.P7
