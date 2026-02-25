/-
  Paper 73: Reverse Direction — BISH Morphisms → Conjecture D

  The new result. If morphism equality in a realization-compatible
  motivic category is BISH-decidable, then Conjecture D must hold.

  Proof (contrapositive):
  Assume Conjecture D fails. Then the radical is non-detachable.
  Morphism cost = LPO ≠ BISH. So BISH morphisms fail.

  The mathematical content behind the axiom:
  If Conjecture D fails, there exist cycles Z that are numerically
  trivial (Z·W = 0 for all W) but homologically nontrivial (cl(Z) ≠ 0).
  A realization-compatible category must distinguish Z from 0
  (since cl(Z) ≠ cl(0)). But detecting Z requires ℚ_ℓ zero-testing.
  Paper 46 Theorem T4a: this encodes LPO.

  The "Jannsen escape" doesn't work:
  Jannsen (1992) showed numerical motives are semisimple even without
  Conjecture D. So one could use numerical motives and get BISH.
  But this sacrifices realization-compatibility: numerical motives
  identify cycles that cohomology distinguishes. The realization
  functor is not faithful. For the "correct" motivic category
  (faithful realization), Conjecture D is necessary.

  References: Paper 46 (encoding, LPO), Jannsen (1992),
    Grothendieck (Standard Conjectures, 1969).
-/
import Papers.P73_Axiom1Reverse.Forward

open CRMLevel RadicalStatus

-- ============================================================
-- The Radical-Morphism Equivalence
-- ============================================================

/-- **Radical determines decidability (structural):**
    Conjecture D holds iff the radical is detachable. -/
theorem conjD_iff_detachable (r : RadicalStatus) :
    conjD_holds r = true ↔ r = detachable := by
  cases r
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact ⟨fun h => Bool.noConfusion h, fun h => RadicalStatus.noConfusion h⟩

-- ============================================================
-- The Main Equivalence
-- ============================================================

/-- **THEOREM B (Morphism-Decidability Equivalence):**
    morphism_cost r = BISH ↔ r = detachable.

    Forward: Conjecture D (detachable) → BISH morphisms.
    Reverse: BISH morphisms → detachable radical → Conjecture D
             (contrapositive: non-detachable → LPO → not BISH).

    This is the Axiom 1 analogue of Paper 72's Theorem B
    (height_search_equivalence). The same logical structure:
    positive-definite height ↔ BISH cycle-search (Paper 72)
    detachable radical ↔ BISH morphism decidability (Paper 73). -/
theorem morphism_decidability_equivalence (r : RadicalStatus) :
    morphism_cost r = BISH ↔ r = detachable := by
  constructor
  · intro h
    cases r
    · rfl
    · -- non_detachable: derive contradiction
      unfold morphism_cost at h
      rw [no_conjD_morphism_cost_eq] at h
      -- h : LPO = BISH — contradiction
      contradiction
  · intro h
    rw [h]
    exact conjD_gives_BISH

-- ============================================================
-- Realization-Compatibility Constraint
-- ============================================================

/-- **COROLLARY (Jannsen obstruction):**
    Without Conjecture D, you cannot have BOTH:
    (1) BISH-decidable morphisms, AND
    (2) faithful ℓ-adic realization.

    - Numerical motives: (1) holds, (2) fails.
    - Homological motives: (2) holds, (1) fails (costs LPO).
    - With Conjecture D: both hold. -/
theorem jannsen_obstruction :
    morphism_cost (standard_without_conjD).radical = LPO := by
  show morphism_cost non_detachable = LPO
  exact no_conjD_gives_LPO

/-- The Jannsen escape: numerical motives are BISH even without Conj D.
    But the realization_compatible flag is false. -/
theorem jannsen_escape :
    morphism_cost (numerical_without_conjD).radical = BISH ∧
    (numerical_without_conjD).realization_compatible = false := by
  constructor
  · show morphism_cost detachable = BISH
    exact conjD_gives_BISH
  · rfl
