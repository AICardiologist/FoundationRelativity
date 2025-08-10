/-
Papers/P2_BidualGap/Gap/C0Spec.lean
Pin‑safe c₀-style predicate and its equivalence with eventual zero for indicator differences.
-/
import Mathlib.Data.Real.Basic
import Papers.P2_BidualGap.Gap.Indicator
import Papers.P2_BidualGap.Gap.IndicatorSpec
import Papers.P2_BidualGap.Gap.IndicatorEventual

namespace Papers.P2.Gap.BooleanSubLattice
open Classical

/-- A pin‑safe "c₀" predicate: tail smallness without topology. -/
def c0Spec (f : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |f n| ≤ ε

/-- Eventually zero ⇒ c0Spec (trivial, since tails are literally 0). -/
lemma eventuallyZero_to_c0Spec {f : ℕ → ℝ} :
    EventuallyZero f → c0Spec f := by
  intro h ε hε
  rcases h with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have := hN n hn
  -- |0| ≤ ε
  simpa [this, hε.le]

/-- Exact shape: `|χ A n - χ B n|` is the indicator of membership in the symmetric difference. -/
lemma abs_indicator_diff_eq (A B : Set ℕ) (n : ℕ) :
    |χ A n - χ B n| = (if n ∈ symmDiff A B then (1 : ℝ) else 0) := by
  classical
  by_cases hA : n ∈ A
  · by_cases hB : n ∈ B
    · -- in both: difference 0
      simp [χ, symmDiff, hA, hB]
    · -- in A only: difference 1
      simp [χ, symmDiff, hA, hB]
  · by_cases hB : n ∈ B
    · -- in B only: difference -1
      simp [χ, symmDiff, hA, hB]
    · -- in neither: difference 0
      simp [χ, symmDiff, hA, hB]

/-- For indicator differences, tail smallness (c0Spec) ⇔ eventual zero. -/
theorem eventuallyZero_iff_c0Spec_indicator (A B : Set ℕ) :
    EventuallyZero (fun n => χ A n - χ B n)
    ↔ c0Spec (fun n => χ A n - χ B n) := by
  constructor
  · -- ⇒
    exact eventuallyZero_to_c0Spec
  · -- ⇐  (pick ε with 0 < ε < 1; then |⋯| can't be 1 anymore)
    intro hc0
    obtain ⟨ε, hε0, hε1⟩ := exists_between (zero_lt_one : (0 : ℝ) < 1)
    obtain ⟨N, hN⟩ := hc0 ε hε0
    refine ⟨N, ?_⟩
    intro n hn
    have hlt1 : |χ A n - χ B n| < 1 :=
      lt_of_le_of_lt (hN n hn) hε1
    -- If n ∈ A △ B, we'd have |⋯| = 1 (contradiction with hlt1).
    have hnot : n ∉ symmDiff A B := by
      classical
      by_contra hmem
      have : |χ A n - χ B n| = 1 := by
        simpa [abs_indicator_diff_eq A B n, hmem]
      exact (lt_irrefl (1 : ℝ)) (by simpa [this] using hlt1)
    -- Outside the symmetric difference, indicators agree ⇒ difference is 0.
    have : χ A n = χ B n :=
      indicator_eq_of_not_mem_symmDiff' (A := A) (B := B) hnot
    simpa [this]

/-- Final spec: finite symmetric difference ⇔ c₀-style tail smallness. -/
theorem indicatorEqModC0_spec_iff_c0Spec (A B : Set ℕ) :
    indicatorEqModC0Spec A B
    ↔ c0Spec (fun n => χ A n - χ B n) := by
  -- Chain your existing bridge with the indicator⇔c0Spec bridge.
  simpa using
    (indicatorEqModC0_spec_iff_eventuallyZero (A := A) (B := B)).trans
      (eventuallyZero_iff_c0Spec_indicator (A := A) (B := B))

end Papers.P2.Gap.BooleanSubLattice