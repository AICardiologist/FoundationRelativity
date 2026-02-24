/-
  Paper 51: The Constructive Archimedean Rescue in BSD
  Main.lean — Root module and axiom audit

  Series: Constructive Reverse Mathematics and Physics
  Depends on: Papers 23 (FT ↔ CompactOptimization), 28 (stratification pattern)

  Main result: For the rank-1 BSD case, given quarantined analytic axioms
  (Gross-Zagier, Kolyvagin, Silverman bound), the search for a generator
  of E(ℚ) lies in an explicit Finset of size O(B²).

  The Archimedean metric (positive-definiteness of ĥ at u = 1) is the
  unique topological modality converting the search from MP (unbounded)
  to BISH (bounded exhaustive search).

  Key theorems:
  - naiveHeight_bounded_of_canonical : BISH height chain
  - bsd_rank_one_finite_search      : main finite search result
  - bsd_stratification              : existential form with explicit bound
  - padic_failure_vacuous           : p-adic failure (logical negative)
  - archimedean_rescue_gap          : quantified gap between BISH and p-adic

  Zero `sorry`s. Zero custom axioms.
-/
import Papers.P51_BSD.ConstructiveBSD

namespace Papers.P51

-- ========================================================================
-- Axiom Audit
-- ========================================================================
-- All theorems report [propext, Classical.choice, Quot.sound].
-- Classical.choice is uniformly present because Mathlib's ℝ type is
-- constructed via classical Cauchy completion. This is an infrastructure
-- artifact shared by ALL Mathlib theorems about ℝ, including Paper 23's
-- BISH results and Paper 28's EL solution.
--
-- The constructive stratification is verified by proof structure:
--   - BISH half: naiveHeight_bounded_of_canonical uses only abs_le + linarith.
--     No MP/LPO hypothesis appears.
--   - Finite search: searchGrid via Finset.Icc (decidable bounded search).
--   - BSD axioms enter as hypotheses (BSDRankOneData structure fields),
--     NOT as Lean `axiom` declarations.
--
-- Verification: NO custom axiom names should appear below.
-- GrossZagier, KolyvaginRankOne, SilvermanBound, PositiveDefinite
-- are all Prop-valued definitions, not axioms.
--
-- See Paper 10 §Methodology for the full discussion of Classical.choice
-- in Mathlib's ℝ infrastructure.

-- Height bounds (BISH core)
#print axioms naiveHeight_bounded_of_canonical
-- Expected: [propext, Classical.choice, Quot.sound]

#print axioms height_bound_monotone
-- Expected: does not depend on any axioms (pure ℝ arithmetic)

#print axioms height_bound_nonneg
-- Expected: does not depend on any axioms (pure ℝ arithmetic)

-- Search space (finite grid)
#print axioms point_in_grid_of_height_bound
-- Expected: [propext, Classical.choice, Quot.sound]

#print axioms finite_search_space
-- Expected: [propext, Classical.choice, Quot.sound]

-- Main theorems
#print axioms heegner_height_positive
-- Expected: [propext, Classical.choice, Quot.sound]

#print axioms bsd_rank_one_finite_search
-- Expected: [propext, Classical.choice, Quot.sound]

#print axioms bsd_stratification
-- Expected: [propext, Classical.choice, Quot.sound]

-- Logical negative (p-adic failure)
#print axioms padic_failure_vacuous
-- Expected: [propext, Classical.choice, Quot.sound]

#print axioms archimedean_rescue_gap
-- Expected: [propext, Classical.choice, Quot.sound]

-- BISH decidability
#print axioms bish_decidable_of_bound
-- Expected: does not depend on any axioms

end Papers.P51
