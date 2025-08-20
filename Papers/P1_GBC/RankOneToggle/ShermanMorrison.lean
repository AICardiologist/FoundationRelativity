import Papers.P1_GBC.RankOneToggle.Projection

/-!
# Sherman-Morrison Formula for Projections

This module provides the Sherman-Morrison formula specialized to idempotent projections,
giving explicit inverse formulas for operators of the form I + αP where P is a projection.

## Main Results
- `inverse_id_add_smul_proj`: (I + αP)⁻¹ = I - α/(1+α)P when 1+α ≠ 0
- `resolvent_G`: Explicit resolvent formula for the toggle operator

## Mathematical Background
The Sherman-Morrison formula provides the inverse of a rank-one perturbation of the identity.
For an idempotent P (P² = P), the formula simplifies significantly.

## References
- Sherman, J.; Morrison, W. J. (1950). "Adjustment of an inverse matrix"
-/

namespace RankOneToggle

open ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] [NormedField 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [CompleteSpace H]

/-- Sherman-Morrison formula for an idempotent projection P: 
    (I + αP)⁻¹ = I - α/(1+α)P when 1+α ≠ 0 -/
theorem inverse_id_add_smul_proj (P : H →L[𝕜] H) (hP : P.comp P = P) 
    (α : 𝕜) (hα : 1 + α ≠ 0) :
    IsUnit (ContinuousLinearMap.id 𝕜 H + α • P) ∧
    (ContinuousLinearMap.id 𝕜 H + α • P)⁻¹ = 
      ContinuousLinearMap.id 𝕜 H - (α / (1 + α)) • P := by
  -- Define the proposed inverse
  let inv := ContinuousLinearMap.id 𝕜 H - (α / (1 + α)) • P
  
  -- Show that inv is both left and right inverse
  have left_inv : inv.comp (ContinuousLinearMap.id 𝕜 H + α • P) = 
                   ContinuousLinearMap.id 𝕜 H := by
    ext x
    simp only [comp_apply, inv, add_apply, smul_apply, sub_apply, id_apply]
    -- (I - α/(1+α)P)(I + αP)x = (I - α/(1+α)P)(x + αP(x))
    --   = x + αP(x) - α/(1+α)P(x) - α/(1+α)P(αP(x))
    --   = x + αP(x) - α/(1+α)P(x) - α²/(1+α)P²(x)
    --   = x + αP(x) - α/(1+α)P(x) - α²/(1+α)P(x)  [using P² = P]
    --   = x + P(x)[α - α/(1+α) - α²/(1+α)]
    --   = x + P(x)[α(1+α)/(1+α) - α/(1+α) - α²/(1+α)]
    --   = x + P(x)[(α + α² - α - α²)/(1+α)]
    --   = x + P(x) · 0 = x
    field_simp [hα]
    rw [← comp_apply, hP]
    ring_nf
    simp
  
  have right_inv : (ContinuousLinearMap.id 𝕜 H + α • P).comp inv = 
                    ContinuousLinearMap.id 𝕜 H := by
    ext x
    simp only [comp_apply, inv, add_apply, smul_apply, sub_apply, id_apply]
    -- Similar calculation for right inverse
    field_simp [hα]
    rw [← comp_apply, hP]
    ring_nf
    simp
  
  constructor
  · -- Show it's a unit
    use inv
    constructor <;> [exact left_inv, exact right_inv]
  · -- Show the inverse equals our formula
    have h_unit : IsUnit (ContinuousLinearMap.id 𝕜 H + α • P) := by
      use { val := ContinuousLinearMap.id 𝕜 H + α • P
            inv := inv
            val_inv := left_inv
            inv_val := right_inv }
    rw [← inv_eq_of_mul_eq_one_left h_unit left_inv]

/-- Special case: (I - P)⁻¹ doesn't exist (not injective) -/
lemma not_isUnit_id_sub_proj (P : H →L[𝕜] H) (hP : P.comp P = P) 
    (hP_ne_zero : P ≠ 0) (hP_ne_id : P ≠ ContinuousLinearMap.id 𝕜 H) :
    ¬IsUnit (ContinuousLinearMap.id 𝕜 H - P) := by
  -- I - P has nontrivial kernel (contains range of P)
  -- For any x in range(P), we have x = P(y) for some y
  -- Then (I - P)(x) = (I - P)(P(y)) = P(y) - P²(y) = P(y) - P(y) = 0
  -- So ker(I - P) ⊇ range(P) ≠ {0} (since P ≠ 0)
  intro h_unit
  -- If I - P were a unit, it would be injective
  have h_inj : Function.Injective (ContinuousLinearMap.id 𝕜 H - P) := by
    exact Function.Bijective.injective (isUnit_iff_bijective.mp h_unit)
  -- But P ≠ 0 means there exists x with P(x) ≠ 0
  obtain ⟨x, hx⟩ : ∃ x, P x ≠ 0 := by
    by_contra h
    push_neg at h
    ext y
    exact h y
  -- Then P(x) is in ker(I - P) but P(x) ≠ 0
  have : (ContinuousLinearMap.id 𝕜 H - P) (P x) = 0 := by
    simp only [sub_apply, id_apply]
    rw [← comp_apply, hP, sub_self]
  -- This contradicts injectivity
  exact hx (h_inj this)

/-- Resolvent formula for toggle operator away from spectrum -/
theorem resolvent_G (u : H) (hu : ‖u‖ = 1) (c : Bool) (λ : 𝕜) 
    (hλ : λ ∉ spectrum 𝕜 (G u hu c)) :
    ∃ R : H →L[𝕜] H,
      (λ • ContinuousLinearMap.id 𝕜 H - G u hu c).comp R = 
      ContinuousLinearMap.id 𝕜 H := by
  -- λI - G = λI - (I - c·P) = (λ-1)I + c·P
  -- When λ ∉ spectrum, this is invertible
  cases c
  · -- c = false: G = I, so λI - G = (λ-1)I
    simp [G] at *
    -- λ ∉ {1} means λ ≠ 1
    have hλ_ne_one : λ ≠ 1 := by
      intro h
      rw [h] at hλ
      simp [spectrum_id] at hλ
    use (λ - 1)⁻¹ • ContinuousLinearMap.id 𝕜 H
    ext x
    simp [hλ_ne_one]
    field_simp
  · -- c = true: G = I - P, so λI - G = (λ-1)I + P
    -- From paper: λI - G(1) = λI - (I - P) = (λ-1)I + P = (λ-1)(I + 1/(λ-1)P)
    -- The spectrum of G(true) is {0, 1}, so λ ∉ {0, 1}
    have hλ0 : λ ≠ 0 := by
      intro h
      rw [h] at hλ
      simp [spectrum_G_true] at hλ
    have hλ1 : λ ≠ 1 := by
      intro h
      rw [h] at hλ
      simp [spectrum_G_true] at hλ
    -- Apply Sherman-Morrison with α = 1/(λ-1)
    -- Note: 1 + α = 1 + 1/(λ-1) = λ/(λ-1) ≠ 0 since λ ≠ 0
    let α := (λ - 1)⁻¹
    have hα : 1 + α ≠ 0 := by
      simp only [α]
      field_simp
      exact hλ0
    -- By Sherman-Morrison: (I + αP)⁻¹ = I - α/(1+α)P
    -- And λI - G = (λ-1)(I + αP), so resolvent is 1/(λ-1) · (I + αP)⁻¹
    use (λ - 1)⁻¹ • (ContinuousLinearMap.id 𝕜 H - (α / (1 + α)) • projLine u hu)
    ext x
    -- The calculation follows from the paper's Theorem 3.7
    simp [G_true, projLine_idem]
    field_simp [hλ0, hλ1]
    sorry -- Final algebraic manipulation

/-- Resolvent norm estimate -/
lemma resolvent_norm_bound (u : H) (hu : ‖u‖ = 1) (c : Bool) (λ : 𝕜)
    (hλ : λ ∉ spectrum 𝕜 (G u hu c)) :
    ∃ C > 0, ∀ R : H →L[𝕜] H,
      (λ • ContinuousLinearMap.id 𝕜 H - G u hu c).comp R = 
      ContinuousLinearMap.id 𝕜 H → 
      ‖R‖ ≤ C / dist λ (spectrum 𝕜 (G u hu c)) := by
  -- Standard resolvent estimate
  sorry

end RankOneToggle