/-
Papers/P17_BHEntropy/Entropy.lean
Entropy definitions for the black hole state counting problem.

Defines:
  - count_configs: cardinality of the admissible configuration set
  - entropy: log of the count
  - entropy_density: entropy / area

All definitions are noncomputable (involve Set.Finite.toFinset and Real.log)
but represent BISH-computable quantities for rational parameters.
-/
import Papers.P17_BHEntropy.FiniteCount

noncomputable section
namespace Papers.P17

open Real

-- ========================================================================
-- Counting function
-- ========================================================================

/-- Number of admissible spin configurations.
    N(A, γ, δ) = |{config : SpinConfig | admissible A γ δ config}|.
    This is a computable natural number for rational A, γ, δ (Theorem 3.1). -/
def count_configs (A gamma delta : ℝ)
    (hA : A > 0) (hg : gamma > 0) (hd : delta > 0) : ℕ :=
  (admissible_set_finite A gamma delta hA hg hd).toFinset.card

-- ========================================================================
-- Entropy
-- ========================================================================

/-- Black hole entropy: S(A, γ, δ) = log N(A, γ, δ).
    This is a well-defined computable real for any A > 0, γ > 0, δ > 0. -/
def entropy (A gamma delta : ℝ)
    (hA : A > 0) (hg : gamma > 0) (hd : delta > 0) : ℝ :=
  Real.log (count_configs A gamma delta hA hg hd)

-- ========================================================================
-- Entropy density
-- ========================================================================

/-- Entropy density: S(A)/A.
    The quantity whose convergence as A → ∞ is the subject of Parts B and C. -/
def entropy_density (A gamma delta : ℝ)
    (hA : A > 0) (hg : gamma > 0) (hd : delta > 0) : ℝ :=
  entropy A gamma delta hA hg hd / A

-- ========================================================================
-- Basic properties
-- ========================================================================

/-- Entropy is non-negative. Real.log is ≥ 0 for inputs ≥ 1, and = 0 for inputs
    in [0,1). Since count_configs is a ℕ, it's either 0 (log 0 = 0 by convention)
    or ≥ 1 (log ≥ 0). -/
theorem entropy_nonneg (A gamma delta : ℝ)
    (hA : A > 0) (hg : gamma > 0) (hd : delta > 0) :
    0 ≤ entropy A gamma delta hA hg hd := by
  unfold entropy
  rcases Nat.eq_zero_or_pos (count_configs A gamma delta hA hg hd) with h | h
  · simp [h]
  · exact Real.log_nonneg (by exact_mod_cast h)

/-- Entropy density is non-negative (for A > 0). -/
theorem entropy_density_nonneg (A gamma delta : ℝ)
    (hA : A > 0) (hg : gamma > 0) (hd : delta > 0) :
    0 ≤ entropy_density A gamma delta hA hg hd := by
  unfold entropy_density
  exact div_nonneg (entropy_nonneg A gamma delta hA hg hd) (le_of_lt hA)

end Papers.P17
end
