/-
Papers/P2_BidualGap/Gap/IndicatorEventual.lean
Spec bridge: finite symmetric difference ↔ indicator difference is eventually zero.
This is pin-safe (no topology); later we identify EventuallyZero with c₀ membership.
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Papers.P2_BidualGap.Gap.Indicator
import Papers.P2_BidualGap.Gap.IndicatorSpec

namespace Papers.P2.Gap.BooleanSubLattice
open Classical

/-- Spec-level "eventually zero" for real sequences. -/
def EventuallyZero (f : ℕ → ℝ) : Prop :=
  ∃ N, ∀ n ≥ N, f n = 0

section
variable {A B : Set ℕ}

/-- If `n ∈ A △ B`, the indicators differ at `n`. -/
lemma indicator_ne_of_mem_symmDiff {n : ℕ}
    (h : n ∈ symmDiff A B) :
    χ A n ≠ χ B n := by
  -- expand `A △ B = (A \ B) ∪ (B \ A)`
  have h' : n ∈ (A \ B) ∪ (B \ A) := by simpa [symmDiff] using h
  rcases h' with hAB | hBA
  · rcases hAB with ⟨hA, hnotB⟩
    -- χ_A(n) = 1, χ_B(n) = 0
    simp [χ, hA, hnotB]
  · rcases hBA with ⟨hB, hnotA⟩
    -- χ_A(n) = 0, χ_B(n) = 1
    simp [χ, hnotA, hB]

/-- If `n ∉ A △ B`, the indicators agree at `n`. (already available; restated for convenience) -/
lemma indicator_eq_of_not_mem_symmDiff' {n : ℕ}
    (hn : n ∉ symmDiff A B) : χ A n = χ B n :=
  indicator_eq_of_not_mem_symmDiff (A := A) (B := B) (n := n) hn

/-- Finite symmetric difference ⇒ indicator difference is eventually zero. -/
theorem indicatorSpec_implies_eventuallyZero
    {A B : Set ℕ}
    (hfin : (symmDiff A B).Finite) :
    EventuallyZero (fun n => χ A n - χ B n) := by
  classical
  -- Turn the finite set into a finset `s`.
  set s : Finset ℕ := hfin.toFinset with hs
  -- Coe back to a set: `symmDiff A B = (s : Set ℕ)`.
  have hcoe : symmDiff A B = (s : Set ℕ) := by
    -- `Set.Finite.coe_toFinset hfin : ↑(hfin.toFinset) = symmDiff A B`
    -- so we just flip it and rewrite with `hs`.
    simp [hs, Set.Finite.coe_toFinset hfin]

  -- Two cases: empty vs nonempty.
  by_cases hse : s = ∅
  · -- Empty symmetric difference ⇒ difference is identically zero
    have hempty : symmDiff A B = ∅ := by simp [hcoe, hse]
    refine ⟨0, ?_⟩
    intro n _hn
    have : χ A n = χ B n :=
      indicator_eq_of_not_mem_symmDiff' (A := A) (B := B) (by simp [hempty])
    simp [this]

  · -- Nonempty: use the max element of `s` as a cutoff
    have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hse
    let M := s.max' hne
    refine ⟨M + 1, ?_⟩
    intro n hn
    -- Show `n ∉ A △ B` when `n ≥ M+1`.
    have hnot : n ∉ symmDiff A B := by
      intro hmem
      -- convert set membership to finset membership
      have hmem_s : n ∈ s := by
        -- `n ∈ symmDiff A B` ↔ `n ∈ (s : Set ℕ)` by `hcoe`,
        -- and `n ∈ (s : Set ℕ)` ↔ `n ∈ s` by `Finset.mem_coe`.
        have : n ∈ (s : Set ℕ) := by simpa [hcoe] using hmem
        simpa [Finset.mem_coe] using this
      -- then `n ≤ M` by maximality of `M`
      have hle : n ≤ M := Finset.le_max' s n hmem_s
      -- contradiction with `n ≥ M+1`
      have : M + 1 ≤ M := le_trans hn hle
      exact (not_le.mpr (Nat.lt_succ_self M)) this
    -- Outside the symmetric difference the indicators coincide
    have : χ A n = χ B n :=
      indicator_eq_of_not_mem_symmDiff' (A := A) (B := B) hnot
    simp [this]

/-- Indicator difference is eventually zero ⇒ finite symmetric difference. -/
theorem eventuallyZero_implies_indicatorSpec
    (hev : EventuallyZero (fun n => χ A n - χ B n)) :
    (symmDiff A B).Finite := by
  rcases hev with ⟨N, hN⟩
  -- `A △ B` is contained in `{n | n < N}`: otherwise at `n ≥ N` the difference would be zero.
  have hsubset : symmDiff A B ⊆ ((Finset.range N : Finset ℕ) : Set ℕ) := by
    intro n hn
    have hne : χ A n ≠ χ B n := indicator_ne_of_mem_symmDiff (A := A) (B := B) hn
    have hnlt : n < N := by
      by_contra hnlt
      have hNle : N ≤ n := le_of_not_gt hnlt
      have hzero : χ A n - χ B n = 0 := hN n hNle
      exact hne ((sub_eq_zero.mp hzero))
    -- translate `n < N` to membership in `range N`
    simpa [Finset.mem_coe] using (Finset.mem_range.mpr hnlt)
  -- a subset of a finite set is finite
  exact (Set.Finite.subset ((Finset.range N).finite_toSet) hsubset)

/-- Spec‑level equivalence: finite symmetric difference ↔ eventually zero difference. -/
theorem indicatorEqModC0_spec_iff_eventuallyZero :
    indicatorEqModC0Spec A B ↔ EventuallyZero (fun n => χ A n - χ B n) := by
  constructor
  · intro h; exact indicatorSpec_implies_eventuallyZero (A := A) (B := B) h
  · intro h; exact eventuallyZero_implies_indicatorSpec (A := A) (B := B) h

end
end Papers.P2.Gap.BooleanSubLattice