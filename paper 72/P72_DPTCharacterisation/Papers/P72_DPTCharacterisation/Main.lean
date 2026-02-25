/-
  Paper 72: The DPT Characterisation Theorem
  Archimedean Polarisation Is Necessary — For Cycle-Search

  Main entry point. Zero sorry. All axioms have mathematical references.
  Lean 4 v4.28.0-rc1, Mathlib4.

  v3: The theorem is about cycle-search decidability, NOT abstract
  Tannakian categories. Rep_ℚ(G) is trivially decidable for any G —
  the SL₂ counterexample (v1 review) is valid. The correct level:
  can you FIND algebraic cycles using height bounds? That requires
  Northcott, which requires positive-definiteness, which requires
  u(ℝ) = ∞.

  Design: cycle-search costs are axiomatised (Paper 69 pattern).
  The assembly function maps HeightType to opaque values. Proofs
  invoke axioms explicitly, not definitional unfolding.

  Results:
    Theorem A (Minimality): No proper subset of DPT Axioms 1-3 suffices.
    Theorem B (Height-Search): pos-def height ↔ BISH cycle-search.
    Theorem C (Characterisation): DPT is minimal for BISH motivic arithmetic.
    Corollary: Archimedean Principle is a biconditional for cycle-search.

  Axiom inventory (4 opaque + 4 axiom, all with mathematical references):
    northcott_search_cost      + _eq  → Paper 51 (Silverman/Northcott)
    no_northcott_search_cost   + _eq  → Paper 48 (L(E,1)=0 ↔ LPO)
    without_A1_cost            + _eq  → Paper 46/50 (Conjecture D)
    without_A2_cost            + _eq  → Paper 45 (Weil I eigenvalues)
    (no axiom without reference)
-/
import Papers.P72_DPTCharacterisation.Characterisation

-- Theorem A: minimality
#check dpt_minimality
#check axiom1_necessary
#check axiom2_necessary
#check axiom3_necessary_for_search
#check axiom3_sufficient_for_search

-- Theorem B: height-search equivalence
#check height_search_equivalence
#check positive_definite_gives_BISH
#check indefinite_gives_LPO
#check northcott_iff_positive_definite

-- Theorem C: characterisation
#check archimedean_necessary_for_search
#check dpt_characterisation
#check archimedean_principle_sharpened
