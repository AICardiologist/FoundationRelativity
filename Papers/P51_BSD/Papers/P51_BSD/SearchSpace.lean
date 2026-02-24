/-
  Paper 51: The Constructive Archimedean Rescue in BSD
  SearchSpace.lean — Finite search space construction

  Given a naive height bound h(P) ≤ H, the coordinates (p, q) of P
  satisfy |p|, |q| ≤ exp(H). This gives an explicit finite grid
  Finset.Icc(-B, B) ×ˢ Finset.Icc(-B, B) with B = ⌈exp(H)⌉.

  This is the constructive payoff: the search for a generator becomes
  a bounded exhaustive search over a known finite set — BISH, not MP.

  Zero `sorry`s. Zero custom axioms.
-/
import Papers.P51_BSD.HeightBounds
import Mathlib.Data.Int.Interval

namespace Papers.P51

noncomputable section

-- ========================================================================
-- Search Bound from Height Bound
-- ========================================================================

/-- The integer search bound: given a height bound H, the coordinates
    of any rational point with h(P) ≤ H satisfy |p|, |q| ≤ exp(H).
    We round up to get an integer bound B = ⌈exp(H)⌉. -/
def searchBound (H : ℝ) : ℤ :=
  ⌈Real.exp H⌉

/-- The search bound is positive (since exp(H) > 0 for all H). -/
theorem searchBound_pos (H : ℝ) : 0 < searchBound H := by
  simp only [searchBound]
  exact Int.ceil_pos.mpr (Real.exp_pos H)

/-- The search bound is non-negative. -/
theorem searchBound_nonneg (H : ℝ) : 0 ≤ searchBound H :=
  le_of_lt (searchBound_pos H)

-- ========================================================================
-- Search Grid (Finset)
-- ========================================================================

/-- The search grid: all integer pairs (p, q) with p, q ∈ [-B, B].
    This is the Finset that replaces unbounded Diophantine search. -/
def searchGrid (B : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-B) B) ×ˢ (Finset.Icc (-B) B)

-- ========================================================================
-- Height Bound Implies Coordinate Bound
-- ========================================================================

/-- From naiveHeight P ≤ H, both |p| and |q| are at most exp(H).

    Proof chain:
      h(P) = log(max(|p|, |q|)) ≤ H
      ⟹ max(|p|, |q|) ≤ exp(H)    (since log x ≤ y ↔ x ≤ exp y for x > 0)
      ⟹ |p| ≤ exp(H) and |q| ≤ exp(H) -/
theorem coords_le_exp_of_naiveHeight_le (P : RatPoint) (H : ℝ)
    (hH : naiveHeight P ≤ H) :
    (|P.p| : ℝ) ≤ Real.exp H ∧ (|P.q| : ℝ) ≤ Real.exp H := by
  simp only [naiveHeight] at hH
  have hq_ne : P.q ≠ 0 := P.hq
  have hq_abs : (0 : ℝ) < (|P.q| : ℝ) := by
    exact_mod_cast abs_pos.mpr hq_ne
  have hmax_pos : (0 : ℝ) < max (|P.p| : ℝ) (|P.q| : ℝ) :=
    lt_of_lt_of_le hq_abs (le_max_right _ _)
  have hmax_le : max (|P.p| : ℝ) (|P.q| : ℝ) ≤ Real.exp H :=
    (Real.log_le_iff_le_exp hmax_pos).mp hH
  exact ⟨le_trans (le_max_left _ _) hmax_le, le_trans (le_max_right _ _) hmax_le⟩

-- ========================================================================
-- Auxiliary: integer in Icc from real absolute value bound
-- ========================================================================

/-- If |n| ≤ x as reals, then n ∈ Finset.Icc (-⌈x⌉) ⌈x⌉ as integers.

    Proof: |n| ≤ x gives -x ≤ n ≤ x.
    Then n ≤ x ≤ ⌈x⌉ gives n ≤ ⌈x⌉.
    And -x ≤ n gives -⌈x⌉ = ⌊-x⌋ ≤ ⌊(n : ℝ)⌋ = n, so -⌈x⌉ ≤ n. -/
private theorem int_mem_Icc_of_abs_le_real {n : ℤ} {x : ℝ}
    (h : (|n| : ℝ) ≤ x) : n ∈ Finset.Icc (-⌈x⌉) (⌈x⌉) := by
  rw [Finset.mem_Icc]
  rw [abs_le] at h
  constructor
  · -- -⌈x⌉ ≤ n: cast to ℝ, use -⌈x⌉ ≤ -x ≤ n
    have : ((-⌈x⌉ : ℤ) : ℝ) ≤ (n : ℝ) := by
      calc ((-⌈x⌉ : ℤ) : ℝ) = -(⌈x⌉ : ℝ) := by push_cast; ring
        _ ≤ -x := neg_le_neg (Int.le_ceil x)
        _ ≤ (n : ℝ) := h.1
    exact_mod_cast this
  · -- n ≤ ⌈x⌉: cast to ℝ, use n ≤ x ≤ ⌈x⌉
    have : (n : ℝ) ≤ (⌈x⌉ : ℝ) := le_trans h.2 (Int.le_ceil x)
    exact_mod_cast this

-- ========================================================================
-- Key theorem: height bound gives grid membership
-- ========================================================================

/-- **Key theorem:** if naiveHeight P ≤ H, then (P.p, P.q) is in the
    search grid with bound ⌈exp(H)⌉.

    This is the finiteness step: a height bound converts to grid membership. -/
theorem point_in_grid_of_height_bound (P : RatPoint) (H : ℝ)
    (hH : naiveHeight P ≤ H) :
    (P.p, P.q) ∈ searchGrid (searchBound H) := by
  obtain ⟨hp_le, hq_le⟩ := coords_le_exp_of_naiveHeight_le P H hH
  simp only [searchGrid, searchBound, Finset.mem_product]
  exact ⟨int_mem_Icc_of_abs_le_real hp_le, int_mem_Icc_of_abs_le_real hq_le⟩

end

-- ========================================================================
-- The Fundamental Finite Search Theorem
-- ========================================================================

/-- **BISH Finite Search.** Given Silverman's bound and a canonical
    height bound C, any point P with ĥ(P) ≤ C has coordinates in an
    explicit finite grid.

    This is the constructive core: the search is bounded, hence BISH.
    No Markov's Principle needed. -/
theorem finite_search_space
    (E : ECData) (canonicalHeight : RatPoint → ℝ)
    (hS : SilvermanBound E canonicalHeight)
    (C : ℝ) (P : RatPoint) (hP : canonicalHeight P ≤ C) :
    (P.p, P.q) ∈ searchGrid (searchBound (2 * C + 2 * E.mu)) := by
  apply point_in_grid_of_height_bound
  exact naiveHeight_bounded_of_canonical E canonicalHeight hS P C hP

end Papers.P51
