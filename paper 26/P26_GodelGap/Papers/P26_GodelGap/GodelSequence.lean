/-
Papers/P26_GodelGap/GodelSequence.lean
Paper 26: The Gödel-Gap Correspondence

The Gödel sequence v^φ: the bridge between arithmetic and analysis.
-/
import Papers.P26_GodelGap.ArithmeticSide
import Papers.P26_GodelGap.AnalyticSide

namespace Papers.P26_GodelGap

open Classical

-- ========================================================================
-- The Gödel sequence
-- ========================================================================

/-- The Gödel sequence of a sentence φ with Gödel number g.
    On row g: starts at 1 and drops to 0 once a refutation of φ is found.
    On all other rows: identically 0. -/
noncomputable def godelSeq (φ : SentencePA) : ℕ → ℝ :=
  fun k =>
    if k.unpair.1 = godelNum φ ∧
       ∀ p, p ≤ k → ¬ PrfPA p (negPA φ)
    then 1
    else 0

-- ========================================================================
-- Basic properties
-- ========================================================================

/-- godelSeq is {0,1}-valued. -/
theorem godelSeq_01 (φ : SentencePA) (k : ℕ) :
    godelSeq φ k = 0 ∨ godelSeq φ k = 1 := by
  simp only [godelSeq]
  split_ifs <;> simp

/-- godelSeq is bounded by 1. -/
theorem godelSeq_bdd (φ : SentencePA) : ∃ M : ℝ, ∀ k, |godelSeq φ k| ≤ M := by
  exact ⟨1, fun k => by
    cases godelSeq_01 φ k with
    | inl h => simp [h]
    | inr h => simp [h]⟩

/-- godelSeq as a bounded sequence (element of ℓ∞). -/
noncomputable def godelSeqBdd (φ : SentencePA) : BddSeq :=
  ⟨godelSeq φ, godelSeq_bdd φ⟩

-- ========================================================================
-- Refutable sentences: godelSeq ∈ c₀
-- ========================================================================

/-- If φ is refutable, godelSeq φ is eventually zero. -/
theorem godelSeq_refutable_eventually_zero (φ : SentencePA)
    (href : RefutablePA φ) :
    ∃ N, ∀ k ≥ N, godelSeq φ k = 0 := by
  obtain ⟨p₀, hp₀⟩ := href
  exact ⟨p₀, fun k hk => by
    simp only [godelSeq]
    rw [if_neg]
    push_neg
    intro _hrow
    exact ⟨p₀, hk, hp₀⟩⟩

/-- If φ is refutable, godelSeq φ converges to 0 (is in c₀). -/
theorem godelSeq_refutable_null (φ : SentencePA) (href : RefutablePA φ) :
    Filter.Tendsto (godelSeq φ) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := godelSeq_refutable_eventually_zero φ href
  exact ⟨N, fun k hk => by simp [hN k hk, dist_self]; exact hε⟩

-- ========================================================================
-- Consistent sentences: godelSeq ∉ c₀
-- ========================================================================

/-- If φ is consistent, then godelSeq φ = 1 on all of row (godelNum φ). -/
theorem godelSeq_consistent_on_row (φ : SentencePA) (hcon : ConsistentPA φ)
    (k : ℕ) (hrow : k.unpair.1 = godelNum φ) :
    godelSeq φ k = 1 := by
  simp only [godelSeq]
  rw [if_pos]
  exact ⟨hrow, fun p _hp hprf => hcon ⟨p, hprf⟩⟩

/-- If φ is consistent, godelSeq φ has infinitely many 1s. -/
theorem godelSeq_consistent_infinite_ones (φ : SentencePA)
    (hcon : ConsistentPA φ) :
    Set.Infinite {k | godelSeq φ k = 1} := by
  have hsub : row (godelNum φ) ⊆ {k | godelSeq φ k = 1} := by
    intro k hk
    simp only [Set.mem_setOf_eq]
    exact godelSeq_consistent_on_row φ hcon k hk
  exact (row_infinite (godelNum φ)).mono hsub

/-- If φ is consistent, godelSeq φ does NOT converge to 0. -/
theorem godelSeq_consistent_not_null (φ : SentencePA)
    (hcon : ConsistentPA φ) :
    ¬ Filter.Tendsto (godelSeq φ) Filter.atTop (nhds 0) :=
  not_null_of_infinite_ones (godelSeq_01 φ) (godelSeq_consistent_infinite_ones φ hcon)

-- ========================================================================
-- Consistent godelSeq agrees with rowChar mod c₀
-- ========================================================================

/-- If φ is consistent, godelSeq φ = rowChar (godelNum φ) pointwise. -/
theorem godelSeq_consistent_eq_rowChar (φ : SentencePA) (hcon : ConsistentPA φ) :
    ∀ k, godelSeq φ k = rowChar (godelNum φ) k := by
  intro k
  simp only [godelSeq, rowChar]
  by_cases hrow : k.unpair.1 = godelNum φ
  · -- On row g: the "no refutation" condition holds (φ is consistent)
    have hno_ref : ∀ p, p ≤ k → ¬ PrfPA p (negPA φ) :=
      fun p _hp hprf => hcon ⟨p, hprf⟩
    rw [if_pos ⟨hrow, hno_ref⟩, if_pos hrow]
  · -- Off row g: both are 0
    rw [if_neg (by push_neg; intro h; exact absurd h hrow), if_neg hrow]

/-- If φ is consistent, [godelSeq φ] = [rowChar (godelNum φ)] in ℓ∞/c₀. -/
theorem godelSeq_consistent_class (φ : SentencePA) (hcon : ConsistentPA φ) :
    bddSeqEquiv (godelSeqBdd φ) (rowCharBdd (godelNum φ)) := by
  simp only [bddSeqEquiv, godelSeqBdd, rowCharBdd]
  have heq : (fun k => godelSeq φ k - rowChar (godelNum φ) k) = fun _ => 0 := by
    ext k; rw [godelSeq_consistent_eq_rowChar φ hcon k]; ring
  rw [heq]
  exact tendsto_const_nhds

/-- If φ is refutable, [godelSeq φ] = [0] in ℓ∞/c₀. -/
theorem godelSeq_refutable_class (φ : SentencePA) (href : RefutablePA φ) :
    bddSeqEquiv (godelSeqBdd φ) zeroBdd := by
  simp only [bddSeqEquiv, godelSeqBdd, zeroBdd, zeroSeq]
  have heq : (fun k => godelSeq φ k - 0) = godelSeq φ := by ext; ring
  rw [heq]
  exact godelSeq_refutable_null φ href

-- ========================================================================
-- The Gödel-Gap map Φ (raw, on sentences)
-- ========================================================================

/-- The Gödel-Gap map on sentences. -/
noncomputable def godelGapRaw (φ : SentencePA) : BidualGap :=
  BidualGap.mk (godelSeqBdd φ)

/-- PA-equivalent sentences produce the same gap "type". -/
theorem paEquiv_gap_type (φ ψ : SentencePA) (h : PAEquiv φ ψ) :
    (ConsistentPA φ ↔ ConsistentPA ψ) := paEquiv_consistent_iff φ ψ h

end Papers.P26_GodelGap
