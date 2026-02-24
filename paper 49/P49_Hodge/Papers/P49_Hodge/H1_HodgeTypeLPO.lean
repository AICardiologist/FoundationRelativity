/-
  Paper 49: Hodge Conjecture — Lean 4 Formalization
  H1_HodgeTypeLPO.lean: Theorem H1 — Hodge Type (r,r) ↔ LPO

  Main result (Theorem H1):
    (∀ x, is_hodge_type_rr x ∨ ¬ is_hodge_type_rr x) ↔ LPO_C

  (⇒) Given decidability of Hodge type, we can decide whether
  any scalar z : ℂ is zero by encoding it into a class whose
  Hodge type status depends on z = 0.

  (⇐) Given LPO on ℂ, we can test each coordinate of
  hodge_projection_complement(x) for zero, yielding decidable
  Hodge type.

  This parallels Paper 46 Theorem T1 (Galois-invariance ↔ LPO),
  substituting the Hodge complement projection for ker(Frob - I).

  Axiom profile: encode_scalar_to_hodge_type, LPO_decides_hodge_type
  No sorry.
-/

import Papers.P49_Hodge.Defs

noncomputable section

namespace Papers.P49

-- ============================================================
-- Forward Direction: Hodge Type Decidability → LPO
-- ============================================================

/-- **H1a: Deciding Hodge type requires LPO.**

    If Hodge type (r,r) is decidable for all x ∈ H_C,
    then every scalar z ∈ ℂ is decidably zero or nonzero.

    Proof: For any z : ℂ, the encoding axiom provides x ∈ H_C
    with is_hodge_type_rr x ↔ z = 0. The decidability oracle
    on x then decides z = 0. -/
theorem hodge_type_requires_LPO :
    (∀ (x : H_C), is_hodge_type_rr x ∨ ¬ is_hodge_type_rr x) → LPO_C := by
  intro h_dec z
  -- Encode z into a class whose Hodge type encodes z = 0
  obtain ⟨x, hx⟩ := encode_scalar_to_hodge_type z
  -- The oracle decides is_hodge_type_rr x
  rcases h_dec x with h_in | h_not_in
  · -- x is type (r,r) → z = 0
    left; exact hx.mp h_in
  · -- x is not type (r,r) → z ≠ 0
    right; exact fun hz => h_not_in (hx.mpr hz)

-- ============================================================
-- Reverse Direction: LPO → Hodge Type Decidability
-- ============================================================

/-- **H1b: LPO suffices for deciding Hodge type.**

    If LPO holds for ℂ, then Hodge type (r,r) is decidable
    for all x ∈ H_C.

    Mathematical argument: LPO_C gives decidable equality on ℂ.
    For x ∈ H_C, compute y = hodge_projection_complement(x) and
    express y in coordinates (y₁,...,yₙ). Apply LPO to each yᵢ.
    If all zero, x is type (r,r). If any nonzero, x is not.
    Uses finite-dimensionality of H_C essentially. -/
theorem LPO_decides_hodge_type_thm :
    LPO_C → (∀ (x : H_C), is_hodge_type_rr x ∨ ¬ is_hodge_type_rr x) :=
  LPO_decides_hodge_type

-- ============================================================
-- The Main Theorem H1
-- ============================================================

/-- **Theorem H1 (Hodge Type ↔ LPO).**
    Deciding whether a cohomology class is of Hodge type (r,r)
    (i.e., annihilated by the complement projection) is equivalent
    to the Limited Principle of Omniscience for ℂ.

    This calibrates the abstract side of the Hodge Conjecture:
    testing x ∈ H^{r,r} requires exact zero-testing in ℂ. -/
theorem hodge_type_iff_LPO :
    (∀ (x : H_C), is_hodge_type_rr x ∨ ¬ is_hodge_type_rr x) ↔ LPO_C :=
  ⟨hodge_type_requires_LPO, LPO_decides_hodge_type_thm⟩

end Papers.P49
