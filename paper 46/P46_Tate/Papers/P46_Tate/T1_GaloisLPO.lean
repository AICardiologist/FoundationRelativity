/-
  Paper 46: Tate Conjecture — Lean 4 Formalization
  T1_GaloisLPO.lean: Theorem T1 — Galois-Invariance ↔ LPO

  Main result (Theorem T1):
    (∀ x, x ∈ galois_fixed ∨ x ∉ galois_fixed) ↔ LPO_Q_ell

  (⇒) Given decidability of Galois-invariance, we can decide whether
  any scalar a : ℚ_ℓ is zero by encoding it into a vector whose
  Galois-invariance status depends on a = 0.

  (⇐) Given LPO on ℚ_ℓ, we can test each coordinate of (Frob - I)(x)
  for zero, yielding decidable membership in ker(Frob - I).

  This parallels Paper 45 Theorem C2, substituting Frob - I for the
  abstract spectral sequence differential.

  Axiom profile: encode_scalar_to_galois, LPO_decides_ker_membership
  No sorry.
-/

import Papers.P46_Tate.Defs

noncomputable section

namespace Papers.P46

-- ============================================================
-- Forward Direction: Galois Decidability → LPO
-- ============================================================

/-- **T1a: Deciding Galois-invariance requires LPO.**

    If membership in ker(Frob - I) is decidable for all x ∈ V,
    then every scalar a ∈ ℚ_ℓ is decidably zero or nonzero.

    Proof: For any a : ℚ_ℓ, the encoding axiom provides x ∈ V
    with x ∈ galois_fixed ↔ a = 0. The decidability oracle on x
    then decides a = 0. -/
theorem galois_invariance_requires_LPO :
    (∀ (x : V), x ∈ galois_fixed ∨ x ∉ galois_fixed) → LPO_Q_ell := by
  intro h_dec a
  -- Encode a into a vector whose Galois-invariance encodes a = 0
  obtain ⟨x, hx⟩ := encode_scalar_to_galois a
  -- The oracle decides x ∈ galois_fixed
  rcases h_dec x with h_in | h_not_in
  · -- x ∈ galois_fixed → a = 0
    left; exact hx.mp h_in
  · -- x ∉ galois_fixed → a ≠ 0
    right; exact fun ha => h_not_in (hx.mpr ha)

-- ============================================================
-- Reverse Direction: LPO → Galois Decidability
-- ============================================================

/-- **T1b: LPO suffices for deciding Galois-invariance.**

    If LPO holds for ℚ_ℓ, then membership in ker(Frob - I)
    is decidable for all x ∈ V.

    Mathematical argument: LPO_Q_ell gives decidable equality
    on ℚ_ℓ. For x ∈ V, compute y = (Frob - I)(x) and express
    y in coordinates (y₁,...,yₙ). Apply LPO to each yᵢ.
    If all zero, x ∈ ker(Frob - I). If any nonzero, x ∉ ker.
    Uses finite dimensionality of V essentially. -/
theorem LPO_decides_galois_invariance :
    LPO_Q_ell → (∀ (x : V), x ∈ galois_fixed ∨ x ∉ galois_fixed) :=
  LPO_decides_ker_membership

-- ============================================================
-- The Main Theorem T1
-- ============================================================

/-- **Theorem T1 (Galois-Invariance ↔ LPO).**
    Deciding whether a cohomology class is Galois-invariant
    (i.e., fixed by the arithmetic Frobenius) is equivalent to
    the Limited Principle of Omniscience for ℚ_ℓ.

    This calibrates the abstract side of the Tate Conjecture:
    testing x ∈ V^{F=1} requires exact zero-testing in ℚ_ℓ. -/
theorem galois_invariance_iff_LPO :
    (∀ (x : V), x ∈ galois_fixed ∨ x ∉ galois_fixed) ↔ LPO_Q_ell :=
  ⟨galois_invariance_requires_LPO, LPO_decides_galois_invariance⟩

end Papers.P46
