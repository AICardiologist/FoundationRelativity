import Mathlib.Analysis.Normed.Algebra.Spectrum

open scoped ComplexConjugate

/-- Test lemma: The spectrum of the identity operator is the singleton `{1}`. -/
lemma spectrum_one_test
    {E : Type*} [NormedRing E] [NormedAlgebra ℂ E] :
    spectrum ℂ (1 : E) = {1} := by
  ext z
  simp [spectrum.mem_iff]
  constructor
  · intro hλ
    by_contra hne
    have : IsUnit ((z - 1) • (1 : E)) := isUnit_smul_of_ne_zero hne isUnit_one
    exact hλ this
  · rintro rfl _
    simp