/-
  Paper 70: The Archimedean Principle
  Why Physics and Number Theory Share a Logical Architecture
  (Paper 70 / capstone, Constructive Reverse Mathematics Series)

  Author: Paul C.-K. Lee, February 2026

  Formally verifies:
    1. CRM hierarchy and domain profiles (Defs.lean)
    2. Weil RH from CRM axioms — the motivic two-liner (WeilRH.lean)
    3. Ramanujan asymmetry — automorphic CRM incompleteness (Ramanujan.lean)
    4. Three spectral gaps as Σ⁰₂ + MP gap theorem (SpectralGaps.lean)
    5. DPT assembly + the Archimedean Principle (ArchimedeanPrinciple.lean)

  Zero sorry. Every axiom has a mathematical reference.
-/
import Papers.P70_Archimedean.Defs
import Papers.P70_Archimedean.WeilRH
import Papers.P70_Archimedean.Ramanujan
import Papers.P70_Archimedean.SpectralGaps
import Papers.P70_Archimedean.ArchimedeanPrinciple

-- ============================================================
-- Verification: all key theorems type-check
-- ============================================================

-- Weil RH from CRM axioms (motivic two-liner)
#check weil_RH_from_CRM

-- Automorphic CRM incompleteness (ℤ witness)
#check automorphic_crm_incomplete
#check unitary_exceeds_ramanujan
#check witness_family

-- Three spectral gaps (Σ⁰₂ structure)
#check three_gaps_same_structure

-- MP gap (projection vs search)
#check mp_gap
#check descent_gap_strict

-- The Archimedean Principle (main theorem)
#check the_archimedean_principle
#check archimedean_removal
#check archimedean_presence
#check archimedean_sole_source
