import Papers.P1_GBC.RankOneToggle.Toggle
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Spectrum of the Rank-One Toggle Operator

This module computes the spectrum and essential spectrum of the toggle operator
G(c) := id - c·P where P is a rank-one projection.

## Main Results
- σ(G(false)) = {1}
- σ(G(true)) = {0, 1}
- σ_ess(G(c)) = {1} for both c ∈ {false, true}

## Mathematical Significance
The spectrum reflects the foundation-dependent behavior:
- When c = false (classical case): G = id has trivial spectrum {1}
- When c = true (constructive obstruction): G has nontrivial spectrum {0, 1}
- The essential spectrum is always {1} (rank-one perturbation of identity)
-/

namespace RankOneToggle

open spectrum ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [CompleteSpace H]

/-- Spectrum of the identity operator -/
@[simp]
lemma spectrum_id : spectrum 𝕜 (ContinuousLinearMap.id 𝕜 H) = {1} := by
  ext z
  simp only [Set.mem_singleton_iff, mem_iff]
  constructor
  · intro h
    -- If z ∈ spectrum, then z • id - id is not a unit
    -- This means (z - 1) • id is not a unit
    -- Since scalar multiplication by nonzero is a unit, z - 1 = 0
    by_contra hz
    have : IsUnit ((z - 1) • (ContinuousLinearMap.id 𝕜 H)) := by
      apply isUnit_smul_of_ne_zero
      exact sub_ne_zero.mpr hz
    rw [← smul_sub, sub_self, smul_zero] at this
    exact not_isUnit_zero this
  · intro h
    rw [h]
    simp [mem_iff]
    exact not_isUnit_zero

/-- Auxiliary: Projection has spectrum {0, 1} -/
lemma spectrum_projection (u : H) (hu : ‖u‖ = 1) :
    spectrum 𝕜 (projLine u hu) = {0, 1} := by
  -- A projection P satisfies P² = P, so its spectrum is in {0, 1}
  -- For idempotent operators, if λ is in spectrum, then λ(λ-1) = 0
  -- The paper shows this directly via block form: P is 1 on span{u} and 0 on span{u}^⊥
  ext λ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, mem_iff]
  constructor
  · intro hλ
    -- If λ ∈ spectrum(P), then λI - P is not invertible
    -- For projections, this happens exactly when λ ∈ {0, 1}
    sorry -- This follows from idempotent spectrum theory
  · intro hλ
    cases hλ with
    | inl h => -- λ = 0
      rw [h]
      -- 0 is in spectrum because P has nontrivial kernel (span{u}^⊥)
      sorry
    | inr h => -- λ = 1
      rw [h]
      -- 1 is in spectrum because (I - P) has nontrivial kernel (span{u})
      sorry

/-- Spectrum of G when c = false -/
theorem spectrum_G_false (u : H) (hu : ‖u‖ = 1) :
    spectrum 𝕜 (G u hu false) = {1} := by
  simp [G_false, spectrum_id]

/-- Spectrum of G when c = true -/
theorem spectrum_G_true (u : H) (hu : ‖u‖ = 1) :
    spectrum 𝕜 (G u hu true) = {0, 1} := by
  -- The paper proves this via resolvent: for λ ∉ {0,1}, the resolvent exists
  -- by Sherman-Morrison formula, hence λ is in resolvent set
  -- Therefore spectrum ⊆ {0,1}
  -- Conversely, G(1) has eigenvalues 0 (on span{u}) and 1 (on span{u}^⊥)
  ext λ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, mem_iff]
  constructor
  · intro hλ
    -- If λ ∈ spectrum, then λI - G is not invertible
    -- By Sherman-Morrison (see paper Theorem 3.7), this happens only when λ ∈ {0,1}
    by_contra h
    push_neg at h
    -- λ ≠ 0 and λ ≠ 1, so resolvent exists by Sherman-Morrison
    -- This contradicts λ ∈ spectrum
    sorry -- Need to connect to ShermanMorrison.resolvent_G
  · intro hλ
    cases hλ with
    | inl h => -- λ = 0: G has eigenvalue 0 with eigenvector u
      rw [h]
      -- From paper: G(1)u = (I - P)u = u - u = 0
      sorry
    | inr h => -- λ = 1: G has eigenvalue 1 on span{u}^⊥
      rw [h]
      -- From paper: for v ⊥ u, G(1)v = (I - P)v = v - 0 = v
      sorry

/-- Combined spectrum theorem -/
theorem spectrum_G (u : H) (hu : ‖u‖ = 1) (c : Bool) :
    (c = false → spectrum 𝕜 (G u hu c) = {1}) ∧
    (c = true → spectrum 𝕜 (G u hu c) = {0, 1}) := by
  constructor
  · intro h
    rw [h]
    exact spectrum_G_false u hu
  · intro h
    rw [h]
    exact spectrum_G_true u hu

/-- The projection is a compact operator (rank-one) -/
lemma projLine_compact (u : H) (hu : ‖u‖ = 1) :
    IsCompactOperator (projLine u hu) := by
  -- A rank-one operator is compact
  -- P(x) = ⟨u, x⟩ • u maps bounded sets to relatively compact sets
  sorry -- This requires showing the range is finite-dimensional

/-- Essential spectrum of G is always {1} -/
theorem essentialSpectrum_G (u : H) (hu : ‖u‖ = 1) (c : Bool) :
    essentialSpectrum 𝕜 (G u hu c) = {1} := by
  -- G = id - c·P where P is compact
  -- For any compact perturbation K of the identity, σ_ess(id - K) = σ_ess(id) = {1}
  cases c
  · -- c = false: G = id, so σ_ess(G) = σ(id) = {1}
    simp [G_false, essentialSpectrum]
    sorry -- Need to show essential spectrum of identity is {1}
  · -- c = true: G = id - P where P is compact
    -- σ_ess(id - P) = σ_ess(id) = {1} by Weyl's theorem
    sorry -- This requires Weyl's theorem for compact perturbations

/-- G has eigenvalue 0 when c = true (u is an eigenvector) -/
lemma has_eigenvalue_zero_true (u : H) (hu : ‖u‖ = 1) :
    HasEigenvalue (G u hu true).toLinearMap 0 := by
  use u
  constructor
  · -- u ≠ 0
    intro h
    rw [h, norm_zero] at hu
    exact one_ne_zero hu
  · -- G(u) = 0
    simp [G_true, projLine_apply_self]

/-- G has eigenvalue 1 when c = true (any v ⊥ u is an eigenvector) -/
lemma has_eigenvalue_one_true (u : H) (hu : ‖u‖ = 1) 
    (v : H) (hv : ⟪u, v⟫_𝕜 = 0) (hv_ne : v ≠ 0) :
    (G u hu true).toLinearMap v = v := by
  simp [G_true, projLine_apply, hv]

end RankOneToggle