/-
  Paper 46: Tate Conjecture — Lean 4 Formalization
  T4_ConjD.lean: Theorem T4 — Standard Conjecture D as Decidability Axiom

  Main results:
    1. hom_equiv_requires_LPO: Decidability of homological equivalence
       implies LPO for ℚ_ℓ.
    2. conjD_decidabilizes_morphisms: Standard Conjecture D converts
       the LPO-dependent homological equivalence to BISH-decidable
       numerical equivalence.

  This is the key NEW result of Paper 46 beyond the P45 infrastructure.
  It recasts Standard Conjecture D as a decidability axiom:
  - Without Conjecture D: testing cl(Z₁) = cl(Z₂) requires LPO
  - With Conjecture D: testing Z₁ ∼ Z₂ numerically suffices (BISH)

  Axiom profile: encode_scalar_to_hom_equiv, standard_conjecture_D,
                 basis_spans_num_equiv
  No sorry.
-/

import Papers.P46_Tate.T2_CycleVerify

noncomputable section

namespace Papers.P46

-- ============================================================
-- §1. Homological Equivalence Requires LPO
-- ============================================================

/-- **T4a: Deciding homological equivalence requires LPO.**

    If we can decide whether cl(Z₁) = cl(Z₂) in V over ℚ_ℓ for
    all pairs of cycles, then we can decide whether any scalar
    a ∈ ℚ_ℓ is zero.

    Proof: For any a : ℚ_ℓ, the encoding axiom provides cycles Z₁, Z₂
    with hom_equiv(Z₁, Z₂) ↔ a = 0. The decidability oracle on
    (Z₁, Z₂) then decides a = 0.

    This is the cycle-class analogue of Theorem T1: testing equality
    in ℚ_ℓ-cohomology inherently requires field-theoretic omniscience. -/
theorem hom_equiv_requires_LPO :
    (∀ (Z₁ Z₂ : ChowGroup), Decidable (hom_equiv Z₁ Z₂)) → LPO_Q_ell := by
  intro h_dec a
  -- Encode a into cycles whose homological equivalence encodes a = 0
  obtain ⟨Z₁, Z₂, hZ⟩ := encode_scalar_to_hom_equiv a
  -- The oracle decides hom_equiv Z₁ Z₂
  cases h_dec Z₁ Z₂ with
  | isTrue h =>
    -- hom_equiv Z₁ Z₂ holds → a = 0
    left; exact hZ.mp h
  | isFalse h =>
    -- hom_equiv Z₁ Z₂ fails → a ≠ 0
    right; exact fun ha => h (hZ.mpr ha)

-- ============================================================
-- §2. Bridge: Finite Basis Spans Numerical Equivalence
-- ============================================================

/-- **Axiom: A finite complementary basis detects numerical equivalence.**

    Given a finite basis {W₁,...,Wₘ} for CH^r(X), numerical equivalence
    Z₁ ∼ Z₂ (i.e., ∀ W, intersection Z₁ W = intersection Z₂ W) is
    equivalent to the finite check on basis elements alone.

    Mathematical justification: Every cycle W is a ℚ-linear combination
    of basis elements. By bilinearity of the intersection pairing,
    intersection(Z, W) is determined by {intersection(Z, Wⱼ)}. -/
axiom basis_spans_num_equiv {m : ℕ} (basis : Fin m → ChowGroup) :
  ∀ (Z₁ Z₂ : ChowGroup), num_equiv Z₁ Z₂ ↔ num_equiv_fin basis Z₁ Z₂

-- ============================================================
-- §3. Standard Conjecture D as Decidability Bridge
-- ============================================================

/-- **T4b: Conjecture D makes homological equivalence decidable in BISH.**

    Standard Conjecture D asserts hom_equiv ↔ num_equiv. Combined with
    the basis spanning axiom, this gives hom_equiv ↔ num_equiv_fin.
    Since num_equiv_fin is BISH-decidable (Theorem T2), homological
    equivalence becomes decidable without LPO.

    This is the main payoff of the Paper 46 calibration:
    Conjecture D is precisely the axiom that DE-OMNISCIENTIZES
    the morphism spaces of the motivic category. -/
def conjD_decidabilizes_morphisms {m : ℕ}
    (basis : Fin m → ChowGroup)
    (Z₁ Z₂ : ChowGroup) :
    Decidable (hom_equiv Z₁ Z₂) := by
  -- Step 1: hom_equiv ↔ num_equiv (Standard Conjecture D)
  --         num_equiv ↔ num_equiv_fin (basis spans)
  rw [show hom_equiv Z₁ Z₂ ↔ num_equiv_fin basis Z₁ Z₂ from
    (standard_conjecture_D Z₁ Z₂).trans (basis_spans_num_equiv basis Z₁ Z₂)]
  -- Step 2: num_equiv_fin is BISH-decidable (Theorem T2)
  exact num_equiv_fin_decidable basis Z₁ Z₂

/-- **Corollary: With Conjecture D, hom_equiv has excluded middle in BISH.** -/
theorem conjD_hom_equiv_em {m : ℕ}
    (basis : Fin m → ChowGroup)
    (Z₁ Z₂ : ChowGroup) :
    hom_equiv Z₁ Z₂ ∨ ¬ hom_equiv Z₁ Z₂ :=
  (conjD_decidabilizes_morphisms basis Z₁ Z₂).em

end Papers.P46
