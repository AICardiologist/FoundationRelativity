/-
  Paper 58: Class Number Correction — Completeness
  Summary theorem: universal identity h · Nm(𝔞) = f verified for all
  split conductors paired with K = ℚ(√-5).
-/
import Papers.P58_ClassNumber.ClassNumberExamples

/-!
# Completeness

The corrected self-intersection formula h · Nm(𝔞) = f is verified for all
four split conductors (f ∈ {7, 9, 61, 163}) paired with K = ℚ(√-5), h_K = 2.
The remaining five conductors (f ∈ {13, 19, 37, 79, 97}) are inert in K
and do not yield CM abelian fourfolds.

For each split conductor:
  - The WeilLatticeData carries the fundamental identity h_num · Nm(𝔞) = f · h_den
  - The Gram matrix determinant satisfies det(G) = f² · |Δ_K| = f² · 20
  - The Steinitz class is uniquely forced by the norm obstruction
-/

-- ========================================================================
-- Section 1: Summary structure
-- ========================================================================

/-- A verified (K, f) pair: Weil lattice data + Gram matrix verification. -/
structure VerifiedPair where
  weil : WeilLatticeData
  gram : VerifiedGramData
  conductors_match : weil.F.conductor = gram.conductor
  steinitz_match : weil.steinitz = gram.steinitz

/-- All four split conductors verified. -/
def allSplitVerified_K5 : List VerifiedPair := [
  ⟨weilData_K5_f7,   verifiedGram_K5_f7,   rfl, rfl⟩,
  ⟨weilData_K5_f9,   verifiedGram_K5_f9,   rfl, rfl⟩,
  ⟨weilData_K5_f61,  verifiedGram_K5_f61,  rfl, rfl⟩,
  ⟨weilData_K5_f163, verifiedGram_K5_f163, rfl, rfl⟩
]

/-- All four split conductors pass verification. -/
theorem four_split_verified_K5 : allSplitVerified_K5.length = 4 := rfl

-- ========================================================================
-- Section 2: The topological volume is an absolute invariant
-- ========================================================================

/-- For every verified pair, det(G) = f² · 20 (the topological volume). -/
theorem all_det_match_K5 (vp : VerifiedPair) (_h : vp ∈ allSplitVerified_K5) :
    vp.gram.gram.det = (vp.gram.conductor : ℤ) ^ 2 * 20 :=
  vp.gram.det_match

-- ========================================================================
-- Section 3: The corrected formula holds universally
-- ========================================================================

/-- For every verified pair, h_num · Nm(𝔞) = f · h_den. -/
theorem all_fundamental_identity_K5 (vp : VerifiedPair) (_h : vp ∈ allSplitVerified_K5) :
    vp.weil.h_num * vp.weil.ideal.ideal_norm =
      vp.weil.F.conductor * vp.weil.h_den :=
  vp.weil.fundamental_identity

-- ========================================================================
-- Section 4: Summary statistics
-- ========================================================================

/-- Paper 58 summary for K = ℚ(√-5):
    - 9 conductors from Papers 56-57
    - 4 split (valid CM fourfolds)
    - 5 inert (no CM fourfold)
    - 2 free (f = 9, 61)
    - 2 non-free (f = 7, 163) -/
theorem paper58_summary_K5 :
    -- Total conductors
    allNineConductors_K5.length = 9 ∧
    -- Split count
    (allNineConductors_K5.filter (fun c => c.steinitz != .inert)).length = 4 ∧
    -- Inert count
    (allNineConductors_K5.filter (fun c => c.steinitz == .inert)).length = 5 ∧
    -- All verified pairs pass
    allSplitVerified_K5.length = 4 := by
  exact ⟨rfl, by native_decide, by native_decide, rfl⟩
