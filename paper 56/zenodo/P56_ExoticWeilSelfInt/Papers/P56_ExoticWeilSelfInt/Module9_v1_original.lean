/-
  Module 9 v1 — HISTORICAL RECORD

  v1 was the original Module 9, which used the discriminant equation
  det(G) = disc(F) as a single axiom. v3 was a superset of v1
  (v3 = v1 + Galois diagonality axiom), so Module9_v3_deprecated.lean
  contains all v1 content plus the additional v3 material.

  Status: WRONG. The discriminant equation det(G) = disc(F) is not
  exact in general. See v2 (the active version) for the correct
  conductor-based derivation.

  The v1 axiom was:
    axiom weil_lattice_disc_eq_field_disc
      (disc_F : ℤ) (d₀ d₁ x : ℤ)
      (h_gram : d₀ * d₁ - x ^ 2 = disc_F) : True

  This is the same axiom that appears in Module9_v3_deprecated.lean.
  No separate v1 source file exists because v3 superseded v1 before
  any version control snapshot was taken.

  For the full v1/v3 code, see Module9_v3_deprecated.lean.
  For the correct v2 code, see GramMatrixDerivation.lean (active).

  Paul C.-K. Lee, February 2026
-/
