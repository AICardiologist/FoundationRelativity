/-
Papers/P16_BornRule/RelativeFreq.lean
Paper 16: The Born Rule as a Logical Artefact.

Theorem 4: Relative frequency of measurement outcomes.
  - relative_freq_nonneg: 0 ≤ freq(i)
  - relative_freq_le_one: freq(i) ≤ 1
  - relative_freq_sum: ∑ freq(i) = 1 (when N > 0)

All BISH — finite counting, rational arithmetic, no choice.
-/
import Papers.P16_BornRule.Defs
import Mathlib.Algebra.BigOperators.Field

namespace Papers.P16

open Finset

-- ========================================================================
-- Partition lemma: counting outcomes gives N
-- ========================================================================

/-- Partitioning Fin N by outcomes gives back N. -/
lemma partition_count {d N : ℕ} (outcomes : Fin N → Fin d) :
    ∑ i : Fin d, (Finset.univ.filter (fun j => outcomes j = i)).card =
    Finset.card (Finset.univ : Finset (Fin N)) := by
  symm
  calc Finset.card (Finset.univ : Finset (Fin N))
      = Finset.card (Finset.univ.biUnion (fun i : Fin d =>
          Finset.univ.filter (fun j => outcomes j = i))) := by
        congr 1; ext j; simp [Finset.mem_biUnion, Finset.mem_filter]
    _ = ∑ i : Fin d, (Finset.univ.filter (fun j => outcomes j = i)).card := by
        rw [Finset.card_biUnion]
        intro x _ y _ hxy
        exact Finset.disjoint_filter.mpr (fun a _ h1 h2 => hxy (h1.symm.trans h2))

-- ========================================================================
-- Relative frequency bounds
-- ========================================================================

/-- Relative frequency is non-negative. -/
theorem relative_freq_nonneg {d N : ℕ} (outcomes : Fin N → Fin d) (i : Fin d) :
    0 ≤ relativeFreq outcomes i := by
  unfold relativeFreq
  positivity

/-- Relative frequency is at most 1. -/
theorem relative_freq_le_one {d N : ℕ} (hN : 0 < N)
    (outcomes : Fin N → Fin d) (i : Fin d) :
    relativeFreq outcomes i ≤ 1 := by
  unfold relativeFreq
  rw [div_le_one (by positivity : (0 : ℝ) < ↑N)]
  have h := Finset.card_filter_le Finset.univ (fun j => outcomes j = i)
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact_mod_cast h

/-- The sum of relative frequencies over all outcomes equals 1 (when N > 0). -/
theorem relative_freq_sum {d N : ℕ} (hN : 0 < N) (_hd : 0 < d)
    (outcomes : Fin N → Fin d) :
    ∑ i : Fin d, relativeFreq outcomes i = 1 := by
  unfold relativeFreq
  rw [← Finset.sum_div, div_eq_one_iff_eq (by positivity : (↑N : ℝ) ≠ 0)]
  have key := partition_count outcomes
  simp at key
  exact_mod_cast key

end Papers.P16
