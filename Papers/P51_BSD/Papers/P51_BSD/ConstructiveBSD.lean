/-
  Paper 51: The Constructive Archimedean Rescue in BSD
  ConstructiveBSD.lean — Main theorems: the Archimedean rescue

  Assembles the full argument:
    1. Gross-Zagier + L'(E,1) > 0  ⟹  ĥ(y_K) > 0
    2. Silverman bound + ĥ(P) ≤ C  ⟹  h(P) ≤ 2C + 2μ
    3. h(P) ≤ H  ⟹  (p,q) ∈ Finset (search grid)
    4. Therefore: BSD rank-1 generator search is BISH

  Also proves the p-adic failure: without positive-definiteness,
  the height bound collapses to h(P) ≤ 2μ, which is vacuously
  useless for finding generators.

  Zero `sorry`s. Zero custom axioms.
-/
import Papers.P51_BSD.BSDAxioms
import Papers.P51_BSD.SearchSpace
import Papers.P51_BSD.Principles

namespace Papers.P51

noncomputable section

-- ========================================================================
-- Step 1: Gross-Zagier + L'(E,1) > 0  ⟹  ĥ(y_K) > 0
-- ========================================================================

/-- From the Gross-Zagier formula and L'(E,1) > 0, the Heegner
    point has positive canonical height: ĥ(y_K) > 0.

    Proof: L'(E,1) = c_GZ · ĥ(y_K) with L'(E,1) > 0 and c_GZ > 0.
    Since c_GZ > 0, we must have ĥ(y_K) > 0. -/
theorem heegner_height_positive (E : ECData) (D : BSDRankOneData E) :
    0 < D.heegner_height := by
  obtain ⟨hGZ, hc⟩ := D.gross_zagier
  -- L'(E,1) = c_GZ * heegner_height with L' > 0 and c_GZ > 0
  -- So heegner_height = L'(E,1) / c_GZ > 0
  nlinarith [D.hL_pos]

-- ========================================================================
-- Step 2: The explicit search bound for rank-1 BSD
-- ========================================================================

/-- The explicit search bound for the rank-1 BSD case:
    B = ⌈exp(2 · ĥ(y_K) + 2μ(E))⌉.

    Any generator P with ĥ(P) ≤ ĥ(y_K) has coordinates in
    the search grid of radius B. -/
noncomputable def bsdSearchBound (E : ECData) (D : BSDRankOneData E) : ℤ :=
  searchBound (2 * D.heegner_height + 2 * E.mu)

-- ========================================================================
-- Step 3: Main Theorem — The Constructive Archimedean Rescue
-- ========================================================================

/-- **Main Theorem: The Constructive Archimedean Rescue.**

    Given the quarantined BSD axioms (Gross-Zagier, Silverman),
    the search for a generator of E(ℚ) in the rank-1 case is bounded:
    any point P with canonical height ĥ(P) ≤ ĥ(y_K) has coordinates
    (P.p, P.q) in an explicit finite grid.

    This converts the MP-level search (find ANY rational point on E)
    into a BISH-level search (check FINITELY MANY candidates).

    The three ingredients:
    1. Gross-Zagier: L'(E,1) > 0 ⟹ ĥ(y_K) > 0 (analytic → algebraic)
    2. Silverman:    ĥ(P) ≤ C ⟹ h(P) ≤ 2C + 2μ (canonical → naive)
    3. Archimedean:  h(P) ≤ B ⟹ finite search (naive → finite grid)

    Without positive-definiteness (ingredient 2's precondition),
    the chain breaks: ĥ(y_K) could be 0 for non-torsion y_K,
    giving no useful height bound, hence no finite search. -/
theorem bsd_rank_one_finite_search
    (E : ECData) (D : BSDRankOneData E)
    (P : RatPoint) (hP : D.canonicalHeight P ≤ D.heegner_height) :
    (P.p, P.q) ∈ searchGrid (bsdSearchBound E D) := by
  exact finite_search_space E D.canonicalHeight D.silverman
    D.heegner_height P hP

-- ========================================================================
-- Step 4: Stratification Statement
-- ========================================================================

/-- **Stratification of BSD search.**

    BISH half: Given the axioms, the generator search is bounded
    by an explicit finite set. No Markov's Principle needed.
    The search terminates by exhaustion.

    The search bound B = ⌈exp(2·ĥ(y_K) + 2μ(E))⌉ is:
    - Positive (from exp > 0)
    - Computable (from Silverman's explicit μ formula)
    - Finite (hence the grid has at most (2B+1)² elements)

    MP half (negative): Without the Archimedean positive-definiteness
    axiom, finding a rational point of infinite order on E/ℚ
    requires unbounded search (MP). See padic_failure_vacuous below. -/
theorem bsd_stratification (E : ECData) (D : BSDRankOneData E) :
    -- Part 1: An explicit finite set contains all candidate generators
    (∃ (B : ℤ), 0 < B ∧
      ∀ P : RatPoint, D.canonicalHeight P ≤ D.heegner_height →
        (P.p, P.q) ∈ searchGrid B) := by
  refine ⟨bsdSearchBound E D, ?_, ?_⟩
  · -- The search bound is positive
    exact searchBound_pos _
  · -- Every candidate is in the grid
    intro P hP
    exact bsd_rank_one_finite_search E D P hP

-- ========================================================================
-- Step 5: The p-adic Failure (logical negative result)
-- ========================================================================

/-- **The p-adic failure.** If the canonical height bound is zero
    (as can happen over ℚ_p where positive-definiteness fails),
    the naive height bound collapses to h(P) ≤ 2μ(E).

    This is vacuously useless: a non-torsion point with ĥ(P) = 0
    would be in a grid of radius ⌈exp(2μ)⌉, but we cannot
    distinguish it from torsion without further non-constructive
    input. The p-adic BSD search remains at the MP level.

    Formally: the bound still holds, but with C = 0 it gives
    no information about which points are generators. -/
theorem padic_failure_vacuous
    (E : ECData) (canonicalHeight : RatPoint → ℝ)
    (hS : SilvermanBound E canonicalHeight)
    (P : RatPoint) (hP : canonicalHeight P ≤ 0) :
    naiveHeight P ≤ 2 * E.mu := by
  have := naiveHeight_bounded_of_canonical E canonicalHeight hS P 0 hP
  linarith

-- ========================================================================
-- Step 6: The Archimedean property is essential
-- ========================================================================

/-- The positive-definiteness of ĥ ensures the Heegner height bound
    is non-trivial: ĥ(y_K) > 0 gives C > 0, hence 2C + 2μ > 2μ,
    strictly enlarging the search space beyond the vacuous p-adic bound.

    This quantifies the "Archimedean rescue": the gap between the
    useful bound (2C + 2μ) and the vacuous bound (2μ) is exactly 2C,
    where C = ĥ(y_K) > 0 thanks to positive-definiteness. -/
theorem archimedean_rescue_gap (E : ECData) (D : BSDRankOneData E) :
    2 * E.mu < 2 * D.heegner_height + 2 * E.mu := by
  linarith [heegner_height_positive E D]

end

end Papers.P51
