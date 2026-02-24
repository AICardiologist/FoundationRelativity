/-
  Paper 49: Hodge Conjecture — Lean 4 Formalization
  H4_CycleVerify.lean: Theorem H4 — Cycle Verification in BISH

  Main results:
    1. intersection_eq_decidable: Integer intersection numbers
       have decidable equality.
    2. cycle_verification_in_HQ_decidable: Verifying cycle_class Z = q
       in H_Q is decidable (H_Q has DecidableEq).
    3. num_equiv_fin_decidable: Numerical equivalence relative to
       a finite basis is decidable.
    4. cycle_verification_BISH: Numerical cycle verification requires
       only integer arithmetic — no omniscience needed.
    5. cycle_verification_in_HC_requires_LPO: Contrast — verifying
       a cycle class in H_C (over ℂ) requires LPO.

  The key insight: intersection numbers land in ℤ, where equality
  is decidable. The cycle class map lands in H_Q, where equality
  is decidable. But if you ask the same question in H_C (the
  complex ambient space), you need LPO.

  No custom axioms beyond Defs.lean infrastructure. No sorry.
-/

import Papers.P49_Hodge.Defs

noncomputable section

namespace Papers.P49

-- ============================================================
-- §1. Integer Intersection Numbers are Decidable
-- ============================================================

/-- Intersection number equality is decidable.
    Since intersection numbers are integers (ℤ), and integer
    equality is decidable, we can computationally verify whether
    two cycles have the same intersection number with any given
    test cycle. -/
def intersection_eq_decidable (Z W : ChowGroup) (n : ℤ) :
    Decidable (intersection Z W = n) :=
  Int.decEq (intersection Z W) n

/-- Intersection number zero-testing is decidable. -/
def intersection_zero_decidable (Z W : ChowGroup) :
    Decidable (intersection Z W = 0) :=
  intersection_eq_decidable Z W 0

-- ============================================================
-- §2. Cycle Verification in H_Q is Decidable
-- ============================================================

/-- **Verifying cycle_class Z = q in H_Q is decidable.**
    This uses DecidableEq on H_Q (axiom): rational cohomology
    classes have computable equality.

    This is the geometric side of the calibration: once a cycle
    is proposed, checking it against a rational class is BISH. -/
def cycle_verification_in_HQ_decidable (Z : ChowGroup) (q : H_Q) :
    Decidable (cycle_class Z = q) :=
  H_Q_decidableEq (cycle_class Z) q

-- ============================================================
-- §3. Numerical Equivalence is Decidable (Finite Basis)
-- ============================================================

/-- **Finite numerical equivalence is decidable.**
    This is a finite conjunction of decidable integer equalities.
    Uses Fintype.decidableForallFintype on the Fin m index type. -/
instance num_equiv_fin_decidable {m : ℕ} (basis : Fin m → ChowGroup)
    (Z₁ Z₂ : ChowGroup) : Decidable (num_equiv_fin basis Z₁ Z₂) :=
  Fintype.decidableForallFintype

-- ============================================================
-- §4. Cycle Verification is BISH
-- ============================================================

/-- **Theorem H4: Cycle verification is BISH-decidable.**

    Given a proposed algebraic cycle Z and a target cycle class,
    verifying numerical equivalence requires only:
    1. Computing intersection numbers (integer arithmetic)
    2. Testing integer equalities (decidable in BISH)

    No omniscience principle is needed. The verification is
    constructive: given Z and a finite complementary basis,
    we can computationally determine whether Z represents the
    target class numerically.

    This contrasts sharply with Hodge type verification (H1),
    which requires LPO for zero-testing in ℂ. -/
theorem cycle_verification_BISH {m : ℕ}
    (basis : Fin m → ChowGroup) (Z₁ Z₂ : ChowGroup) :
    num_equiv_fin basis Z₁ Z₂ ∨ ¬ num_equiv_fin basis Z₁ Z₂ :=
  (num_equiv_fin_decidable basis Z₁ Z₂).em

-- ============================================================
-- §5. Contrast: Verification in H_C Requires LPO
-- ============================================================

/-- **H4e: Verifying a complex class is a cycle class requires LPO.**
    Must check equality in H_C (over ℂ), not H_Q (over ℚ).

    If one can decide whether ι(cl(Z)) = x for all Z and x,
    then one can decide z = 0 for all z : ℂ, i.e., LPO holds.

    This contrast is the essence of the Hodge calibration:
    - In H_Q (rational lattice): verification is BISH ✓
    - In H_C (complex ambient): verification requires LPO ✗
    The Hodge Conjecture asserts that Hodge classes come from
    cycles, converting the H_C question to an H_Q question. -/
theorem cycle_verification_in_HC_requires_LPO :
    (∀ (Z : ChowGroup) (x : H_C),
      rational_inclusion (cycle_class Z) = x ∨
      rational_inclusion (cycle_class Z) ≠ x) → LPO_C := by
  intro h_dec z
  -- Encode z into a cycle-class equation whose truth encodes z = 0
  obtain ⟨Z, x, hx⟩ := encode_scalar_to_cycle_in_HC z
  -- The oracle decides ι(cl(Z)) = x
  rcases h_dec Z x with h_eq | h_ne
  · -- ι(cl(Z)) = x → z = 0
    left; exact hx.mp h_eq
  · -- ι(cl(Z)) ≠ x → z ≠ 0
    right; exact fun hz => h_ne (hx.mpr hz)

end Papers.P49
