/-
  Paper 73: Forward Direction — Conjecture D → BISH Morphisms

  This is the content of Papers 46 and 50, reviewed here for completeness.
  Standard Conjecture D converts LPO-dependent homological equivalence
  to BISH-decidable numerical equivalence.

  The mechanism (Paper 46 T4b):
    Z₁ ~_hom Z₂  ↔  Z₁ ~_num Z₂         (Conjecture D)
                  ↔  ∀j, Z₁·Wⱼ = Z₂·Wⱼ   (finite basis)
                  → BISH                     (integer comparisons)

  References: Paper 46 Theorem T2 (numerical = BISH),
    Paper 46 Theorem T4b (Conj D decidabilises),
    Paper 50 §6 (ConjD.lean).
-/
import Papers.P73_Axiom1Reverse.Defs

open CRMLevel RadicalStatus

-- ============================================================
-- Forward: Conjecture D → BISH Morphisms
-- ============================================================

/-- With Conjecture D, morphism decidability is BISH.
    The radical is detachable: numerical equivalence is decidable
    via finitely many integer intersection tests. -/
theorem conjD_gives_BISH :
    morphism_cost detachable = BISH := by
  unfold morphism_cost
  exact conjD_morphism_cost_eq

/-- Without Conjecture D, realisation-compatible morphism decidability
    requires LPO (homological equivalence needs ℚ_ℓ zero-testing). -/
theorem no_conjD_gives_LPO :
    morphism_cost non_detachable = LPO := by
  unfold morphism_cost
  exact no_conjD_morphism_cost_eq
