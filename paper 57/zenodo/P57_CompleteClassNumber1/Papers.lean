-- Paper 57: Complete Class-Number-1 Landscape for Exotic Weil Self-Intersection
-- Paul C.-K. Lee, February 2026
--
-- Extends Paper 56 to ALL NINE class-number-1 quadratic imaginary fields.
--
-- Module structure:
--   1. NumberFieldData       — 9 trace matrices, disc(F) via native_decide (0 sorry)
--   2. GramMatrixDerivation  — 9 fields, d₀² = disc(F) via cyclic conductor theorem:
--                              disc(F) = conductor² and d₀ = conductor.
--                              (1 principled axiom: weil_class_degree_eq_conductor)
--                              + 9 Gram lattice verifications by norm_num
--                              + non-cyclic counterexample (disc = 229)
--   3. PatternAndVerdict     — 9-row pattern table, HR, DPT verdict (0 sorry)
--
-- Total sorry budget: 1 principled axiom, 0 gaps.
-- MODULE 2 VERSION: v2 (conductor-based). The v1/v3 discriminant equation
-- det(G) = disc(F) is FALSE in general. See GramMatrixDerivation_v3_deprecated.lean.
-- All nine discriminant computations machine-verified.
-- All nine Gram matrix instantiations machine-verified.
-- The class-number-1 landscape is complete.

import Papers.P57_CompleteClassNumber1.NumberFieldData
import Papers.P57_CompleteClassNumber1.GramMatrixDerivation
import Papers.P57_CompleteClassNumber1.PatternAndVerdict
