/-
  Paper 73: Axiom 1 Reverse Characterisation
  Standard Conjecture D Is Necessary for BISH Morphism Decidability

  Main entry point. Zero sorry. All axioms have mathematical references.
  Lean 4 v4.29.0-rc2, Mathlib4.

  The Axiom 1 analogue of Paper 72 (Axiom 3).
  Paper 72: positive-definite height ↔ BISH cycle-search (via Northcott).
  Paper 73: Standard Conjecture D ↔ BISH morphism decidability
            (via radical detachability).

  Results:
    Theorem A (Forward): Conjecture D → BISH morphisms (Paper 46/50).
    Theorem B (Equivalence): Conjecture D ↔ BISH morphisms (new).
    Theorem C (Characterisation): Axiom 1 is necessary and sufficient.
    Corollary: Jannsen obstruction — BISH OR faithful, not both, without D.

  Axiom inventory (4 axioms, all with mathematical references):
    conjD_morphism_cost      + _eq  → Paper 46 T2/T4b, Paper 50 §6
    no_conjD_morphism_cost   + _eq  → Paper 46 T4a (hom_equiv_requires_LPO)
-/
import Papers.P73_Axiom1Reverse.Characterisation

-- Theorem A: forward direction
#check conjD_gives_BISH
#check no_conjD_gives_LPO

-- Theorem B: equivalence
#check morphism_decidability_equivalence
#check conjD_iff_detachable

-- Theorem C: characterisation
#check axiom1_characterisation
#check axiom1_principle_sharpened

-- Jannsen obstruction
#check jannsen_obstruction
#check jannsen_escape
