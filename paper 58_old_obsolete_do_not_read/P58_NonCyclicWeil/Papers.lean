-- Paper 58: Exotic Weil Self-Intersections Beyond the Cyclic Barrier
-- Paul C.-K. Lee, February 2026
--
-- Extends Papers 56-57 to the non-cyclic regime.
--
-- The corrected picture (v2):
--   G is ALWAYS diagonal for K = Q(i) (J-argument: J²=-1, J†=-J).
--   det(G) = d₀² always (a perfect square).
--   For cyclic cubics: d₀ = conductor, disc = conductor² → d₀² = disc.
--   For non-cyclic cubics: disc is NOT a perfect square → d₀² ≠ disc.
--   The "cyclic barrier" is the conductor formula, NOT Gram diagonality.
--
-- Module structure:
--   1. NonCyclicWeil    — Structures, principled axiom, Schoen criterion,
--                         non-squareness of 229, formula failure (1 axiom)
--   2. ReducedForms     — All ten reduced forms for det = 229, completeness
--                         of enumeration, Gauss-Minkowski bound (0 sorry)
--   3. Verdict          — Summary table: nine cyclic + one non-cyclic (0 sorry)
--
-- Total sorry budget: 1 principled axiom, 0 false, 0 gaps.
--   1. schoen_algebraicity (Schoen 1998: norm representability ⟹ algebraic)

import Papers.P58_NonCyclicWeil.NonCyclicWeil
import Papers.P58_NonCyclicWeil.ReducedForms
import Papers.P58_NonCyclicWeil.Verdict
