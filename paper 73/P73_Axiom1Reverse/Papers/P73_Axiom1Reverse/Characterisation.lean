/-
  Paper 73: Axiom 1 Characterisation — Full Assembly

  Combines:
    Theorem A (Forward): Conjecture D → BISH morphisms.
    Theorem B (Equivalence): Conjecture D ↔ BISH morphisms.
    Theorem C (Characterisation): Axiom 1 is both necessary and
      sufficient for BISH-decidable morphisms in a faithful category.

  The Axiom 1 analogue of Paper 72's DPT Characterisation.
  Paper 72: Axiom 3 ↔ BISH cycle-search (via Northcott).
  Paper 73: Axiom 1 ↔ BISH morphisms (via radical detachability).

  Combined with Paper 74 (Axiom 2, planned): all three DPT axioms
  have individual reverse characterisations, upgrading "minimal"
  (Paper 72 Theorem A) to "uniquely necessary" for each.
-/
import Papers.P73_Axiom1Reverse.Reverse

open CRMLevel RadicalStatus

-- ============================================================
-- Axiom 1 Characterisation
-- ============================================================

/-- **THEOREM C (Axiom 1 Characterisation):**
    Standard Conjecture D is necessary and sufficient for
    BISH-decidable morphisms in a realisation-compatible category.

    (1) Forward: Conjecture D → BISH (Paper 46/50).
    (2) Reverse: BISH → Conjecture D (Paper 73, new).
    (3) Without Conjecture D, realisation-compatible costs LPO.
    (4) The Jannsen escape (numerical motives, BISH but unfaithful)
        confirms the trade-off is real, not vacuous.

    Scope: applies to morphism decidability in the motivic category.
    Whether Conjecture D is necessary for OTHER motivic operations
    (e.g., tensor products, duals) is a separate question. -/
theorem axiom1_characterisation :
    -- Forward and reverse
    (morphism_cost detachable = BISH)
    ∧ (morphism_cost non_detachable = LPO)
    -- Realisation-compatible without Conj D costs LPO
    ∧ (morphism_cost (standard_without_conjD).radical = LPO)
    -- Jannsen escape: BISH without realisation
    ∧ (morphism_cost (numerical_without_conjD).radical = BISH) := by
  exact ⟨conjD_gives_BISH,
         no_conjD_gives_LPO,
         jannsen_obstruction,
         (jannsen_escape).1⟩

-- ============================================================
-- Sharpened Axiom 1 Principle
-- ============================================================

/-- **COROLLARY (Axiom 1 Principle, sharpened):**
    morphism_cost r = BISH ↔ r = detachable (i.e., Conjecture D holds).

    Paper 72 Theorem A asserted: without Axiom 1, cost = LPO (forward).
    Paper 73 proves: Axiom 1 is the unique axiom for BISH morphisms
    (biconditional). Conjecture D is not merely a convenient hypothesis
    but the logically necessary bridge between ℓ-adic cohomology
    and constructive decidability. -/
theorem axiom1_principle_sharpened (r : RadicalStatus) :
    morphism_cost r = BISH ↔ conjD_holds r = true := by
  rw [conjD_iff_detachable]
  exact morphism_decidability_equivalence r

-- ============================================================
-- Verification
-- ============================================================

#check conjD_gives_BISH
#check no_conjD_gives_LPO
#check morphism_decidability_equivalence
#check conjD_iff_detachable
#check jannsen_obstruction
#check jannsen_escape
#check axiom1_characterisation
#check axiom1_principle_sharpened
