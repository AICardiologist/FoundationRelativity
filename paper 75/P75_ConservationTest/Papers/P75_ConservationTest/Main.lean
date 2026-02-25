/-
  Paper 75: Conservation Test — Main Entry Point
  CRM Calibration of the Genestier-Lafforgue Semisimple LLC

  Zero sorry. 4 axioms (with mathematical references).
  Lean 4 v4.29.0-rc2, Mathlib4.

  Results:
    Theorem A (Stratification): fs_proof_cost = CLASS.
    Theorem B (Statement): gl_statement_cost = WLPO.
    Theorem C (Conservation Gap): gl_statement_cost < fs_proof_cost.
    Theorem D (DPT Prediction): prediction = observation = WLPO.

  The conservation hypothesis (eliminability of the CLASS gap) is an
  open conjecture discussed in the paper's prose, NOT formalized as
  a Lean axiom. This file verifies the diagnostic results only.

  Axiom inventory (4 axioms, all with mathematical references):
    algebraic_layer_cost   + _eq  → Clausen-Scholze (2019)
    homological_layer_cost + _eq  → Fargues-Scholze (2021), Scholze (2017)
    geometric_layer_cost   + _eq  → Fargues-Scholze (2021), Scholze (2017)
    gl_statement_cost      + _eq  → Bernstein (1984), Paper 74 Thm C
-/
import Papers.P75_ConservationTest.Conservation

-- Theorem A: Stratification
#check fs_proof_cost_is_CLASS
#check algebraic_is_BISH
#check homological_is_CLASS
#check geometric_is_CLASS
#check algebraic_layer_free

-- Theorem B: Statement cost
#check gl_statement_is_WLPO

-- Theorem C: Conservation gap
#check conservation_gap
#check gap_size

-- Theorem D: DPT prediction
#check dpt_prediction_matches

-- FLT analogy
#check gl_harder_than_flt

-- Full assembly
#check conservation_test_assembly
