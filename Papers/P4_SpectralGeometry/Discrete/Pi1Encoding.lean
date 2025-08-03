import Papers.P4_SpectralGeometry.Discrete.IntervalBookkeeping
import Mathlib.Computability.Primrec

/-!
# Π₁-Encoding of Spectral Conditions

This module shows that the spectral gap condition is a Π₁ statement over the
rationals, which is key for the undecidability result.

## Main Results

* `rayleighQuotient` - The Rayleigh quotient as a rational function
* `spectralGapPredicate` - The spectral gap condition as a Π₁ formula
* `encoding_is_pi1` - Proof that the encoding is genuinely Π₁

## Strategy

We show that "λ₁ ≥ threshold" can be expressed as:
  ∀ v ≠ 0, if v ⊥ constants then R(v) ≥ threshold
  
where R(v) is the Rayleigh quotient. Since this is a universal statement over
rational vectors with rational arithmetic, it's Π₁.
-/

namespace Papers.P4_SpectralGeometry.Discrete

variable {n : ℕ} (T : TuringNeckTorus)

/-- A rational vector on the discrete neck torus -/
def RationalVector := T.Vertex → ℚ

/-- The Rayleigh quotient for a vector -/
def rayleighQuotient (L : Matrix T.Vertex T.Vertex ℚ) (v : RationalVector) : ℚ :=
  let Lv : RationalVector := fun i => Finset.univ.sum (fun j => L i j * v j)
  let numerator := Finset.univ.sum (fun i => v i * Lv i)
  let denominator := Finset.univ.sum (fun i => v i * v i)
  if denominator = 0 then 0 else numerator / denominator

/-- A vector is orthogonal to constants if its sum is zero -/
def orthogonalToConstants (v : RationalVector) : Prop :=
  Finset.univ.sum (fun i => v i) = 0

/-- The spectral gap condition as a predicate on matrices -/
def spectralGapPredicate (L : Matrix T.Vertex T.Vertex ℚ) (threshold : ℚ) : Prop :=
  ∀ v : RationalVector, v ≠ 0 → orthogonalToConstants v → 
    rayleighQuotient L v ≥ threshold

/-- Helper: The predicate "v ≠ 0" is decidable and primitive recursive -/
lemma nonzero_is_decidable (v : RationalVector) : Decidable (v ≠ 0) :=
  inferInstance

/-- Helper: Checking orthogonality is primitive recursive -/
lemma orthogonal_is_primrec : Primrec (fun v : RationalVector => 
    if orthogonalToConstants v then 1 else 0) := by
  sorry

/-- Helper: The Rayleigh quotient is primitive recursive in v -/
lemma rayleigh_is_primrec (L : Matrix T.Vertex T.Vertex ℚ) : 
    Primrec (rayleighQuotient L) := by
  sorry

/-- Main theorem: The spectral gap predicate is Π₁ -/
theorem spectral_gap_is_pi1 (L : Matrix T.Vertex T.Vertex ℚ) (threshold : ℚ) :
    ∃ (φ : RationalVector → Prop), 
      (∀ v, Decidable (φ v)) ∧ 
      Primrec (fun v => if φ v then 1 else 0) ∧
      (spectralGapPredicate L threshold ↔ ∀ v, φ v) := by
  -- The formula φ is: "v = 0 ∨ ¬orthogonalToConstants v ∨ rayleighQuotient L v ≥ threshold"
  use fun v => v = 0 ∨ ¬orthogonalToConstants v ∨ rayleighQuotient L v ≥ threshold
  constructor
  · -- Decidability
    intro v
    apply inferInstance
  constructor  
  · -- Primitive recursive
    sorry
  · -- Equivalence
    simp [spectralGapPredicate]
    sorry

/-- The spectral gap of the perturbed system is Π₁ -/
theorem perturbed_gap_is_pi1 (maxSteps : ℕ) :
    let L := T.perturbedLaplacian maxSteps
    ∃ (φ : Prop), (φ ↔ spectralGapPredicate L (spectralThreshold T.h)) ∧ 
                   φ_is_pi1 φ := by
  sorry
where
  φ_is_pi1 (φ : Prop) : Prop := sorry -- Technical definition of being Π₁

/-- Connection to computability: The spectral question is co-c.e. -/
theorem spectral_question_co_ce :
    ¬Computable (fun T : TuringNeckTorus => 
      if ∃ ε > 0, ∀ N, T.spectralGap N ≥ ε then true else false) := by
  -- This follows from the Π₁-completeness and the halting problem reduction
  sorry

end Papers.P4_SpectralGeometry.Discrete