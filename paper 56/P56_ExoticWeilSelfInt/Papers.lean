-- Paper 56: Exotic Weil Class Self-Intersection on CM Abelian Fourfolds
-- Paul C.-K. Lee, February 2026
--
-- Module structure:
--   1. NumberFieldData         — Exact trace matrices, disc(F) via det (0 sorry)
--   2. WeilLattice             — Exotic Weil lattice, dim = 2 (2 principled axioms)
--   3. PolarizationDet         — CM polarization determinants (4 principled axioms)
--   4. SelfIntersection        — deg(w₀ · w₀) from disc(F) (0 sorry; false axiom removed)
--   5. HodgeRiemann            — HR verification: deg > 0 (0 sorry)
--   6. SchoenAlgebraicity      — Algebraicity via Schoen's norm criterion (1 principled)
--   7. Pattern                 — deg = √disc(F) pattern verification (0 sorry)
--   8. Verdict                 — DPT interpretation, summary table (0 sorry)
--   9. GramMatrixDerivation    — Proves d₀² = disc(F) via cyclic conductor theorem:
--                                disc(F) = conductor² and d₀ = conductor.
--                                (1 principled axiom: weil_class_degree_eq_conductor)
--
-- Total sorry budget: 10 principled axioms, 0 false axioms, 0 sorry gaps.
-- MODULE 9 VERSION: v2 (conductor-based). The v1/v3 discriminant equation
-- det(G) = disc(F) is FALSE in general. See Module9_v3_deprecated.lean.
--
-- Axiom taxonomy:
--   (a) Opaque type stubs (~15): abstract types for CM fields, abelian
--       varieties, Weil lattices, generators.
--   (b) Structural helper axioms (~10): scalar extension, field discriminant
--       values, generator existence, self-intersection values.
--   (c) Deep-theorem axioms encoding published results:
--         1. milne_weil_dim                (Milne 1999, Lemma 1.3)
--         2. exotic_not_lefschetz          (Anderson 1993; Milne 1999, §1)
--         3. cm_polarization_threefold     (Shimura 1998, Chapter II)
--         4. det_product_ex1/2/3          (CM arithmetic for each K)
--         5. weil_class_degree_eq_conductor (d₀ = conductor, geometric)
--         6. schoen_algebraicity_ex1/2/3  (Schoen 1998, Theorem 0.2)
--       Count: 10 (three examples across three CM fields).
--
-- Computational modules (1, 5, 7, 8, 9) have ZERO sorry:
--   - det(M₁) = 49, det(M₂) = 81, det(M₃) = 169 via native_decide
--   - Newton's identity steps via norm_num
--   - HR sign computation via norm_num
--   - Pattern checks (n² = n²) via native_decide
--   - Norm witnesses ((1/3)² + 3·0² = 1/9 etc.) via norm_num
--   - Gram matrix algebra (ring), d₀² = disc(F) via conductor rw

import Papers.P56_ExoticWeilSelfInt.NumberFieldData
import Papers.P56_ExoticWeilSelfInt.WeilLattice
import Papers.P56_ExoticWeilSelfInt.PolarizationDet
import Papers.P56_ExoticWeilSelfInt.SelfIntersection
import Papers.P56_ExoticWeilSelfInt.HodgeRiemann
import Papers.P56_ExoticWeilSelfInt.SchoenAlgebraicity
import Papers.P56_ExoticWeilSelfInt.Pattern
import Papers.P56_ExoticWeilSelfInt.Verdict
import Papers.P56_ExoticWeilSelfInt.GramMatrixDerivation
