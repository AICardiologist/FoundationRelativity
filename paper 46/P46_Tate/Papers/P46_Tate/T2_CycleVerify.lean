/-
  Paper 46: Tate Conjecture — Lean 4 Formalization
  T2_CycleVerify.lean: Theorem T2 — Cycle Verification in BISH

  Main results:
    1. intersection_eq_decidable: Integer intersection numbers
       have decidable equality.
    2. num_equiv_fin_decidable: Given a finite complementary basis,
       numerical equivalence is decidable.
    3. cycle_verification_BISH: Cycle verification requires only
       integer arithmetic — no omniscience needed.

  The key insight: intersection numbers land in ℤ, where equality
  is decidable. Given a finite generating set for the relevant Chow
  group, numerical equivalence reduces to finitely many integer
  comparisons. This is a standard decidability argument over
  finite-dimensional modules with integer pairing.

  No custom axioms beyond Defs.lean infrastructure. No sorry.
-/

import Papers.P46_Tate.Defs

noncomputable section

namespace Papers.P46

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
-- §2. Numerical Equivalence is Decidable (Finite Basis)
-- ============================================================

/-- **Numerical equivalence relative to a finite basis is decidable.**

    Given a finite complementary basis {W₁, ..., Wₘ} for CH^r(X),
    numerical equivalence Z₁ ∼ Z₂ reduces to:
      ∀ j ∈ {1,...,m}, intersection Z₁ Wⱼ = intersection Z₂ Wⱼ

    This is a finite conjunction of integer equalities, each
    decidable by Int.decEq. The finite conjunction is decidable
    by Fintype.decidableForallFintype.

    NOTE: Full numerical equivalence quantifies over ALL cycles W,
    which is an infinite universal. The finite basis reduces this
    to a finite check — this reduction is the mathematical content
    that makes numerical equivalence BISH-decidable.

    We formalize the finite version directly, which is the
    computationally meaningful statement. -/
def num_equiv_fin {m : ℕ} (basis : Fin m → ChowGroup)
    (Z₁ Z₂ : ChowGroup) : Prop :=
  ∀ j : Fin m, intersection Z₁ (basis j) = intersection Z₂ (basis j)

/-- Finite numerical equivalence is decidable.
    This is a finite conjunction of decidable integer equalities. -/
instance num_equiv_fin_decidable {m : ℕ} (basis : Fin m → ChowGroup)
    (Z₁ Z₂ : ChowGroup) : Decidable (num_equiv_fin basis Z₁ Z₂) :=
  Fintype.decidableForallFintype

-- ============================================================
-- §3. Cycle Verification is BISH
-- ============================================================

/-- **Theorem T2: Cycle verification is BISH-decidable.**

    Given a proposed algebraic cycle Z and a target cycle class,
    verifying numerical equivalence requires only:
    1. Computing intersection numbers (integer arithmetic)
    2. Testing integer equalities (decidable in BISH)

    No omniscience principle is needed. The verification is
    constructive: given Z and a finite complementary basis,
    we can computationally determine whether Z represents the
    target class numerically.

    This contrasts sharply with homological equivalence, which
    requires zero-testing in ℚ_ℓ (LPO, Theorem T4). -/
theorem cycle_verification_BISH {m : ℕ}
    (basis : Fin m → ChowGroup) (Z₁ Z₂ : ChowGroup) :
    num_equiv_fin basis Z₁ Z₂ ∨ ¬ num_equiv_fin basis Z₁ Z₂ :=
  (num_equiv_fin_decidable basis Z₁ Z₂).em

end Papers.P46
