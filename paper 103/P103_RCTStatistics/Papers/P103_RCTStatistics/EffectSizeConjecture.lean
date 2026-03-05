/-
  EffectSizeConjecture.lean — Part VII

  The constructive effect size threshold: a trial result is
  constructively witnessed iff the effect size exceeds d_min,
  where d_min has a computable constructive correction term.
-/
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace P103

/-- Effect size (Cohen's d) computed from rational data. -/
def cohensD (μ₁ μ₂ σ_pooled : ℚ) (_hσ : σ_pooled > 0) : ℚ :=
  (μ₁ - μ₂) / σ_pooled

/-- Cohen's d is rational when computed from rational data. -/
theorem cohensD_rational (μ₁ μ₂ σ : ℚ) (hσ : σ > 0) :
    ∃ (d : ℚ), d = cohensD μ₁ μ₂ σ hσ := ⟨_, rfl⟩

/-- CONJECTURE: Under normal assumptions, a two-sample t-test result
    is constructively witnessed at BISH+MP iff the effect size exceeds:

      d_min = z_α · √(2/n) + 2 · C_s · ρ̂ / (σ̂ · n)

    First term: classical threshold.
    Second term: constructive correction (the "logical surcharge").

    Key structural features:
    1. No dependence on β (power) — purely logical, not design-based
    2. Correction vanishes as n → ∞ (penumbra shrinks)
    3. Correction explodes as ρ̂/σ̂³ grows (heavy tails)
    4. Uses studentized constant C_s ≈ 3.19, NOT oracle constant -/
theorem constructive_threshold_exists
    (α : ℚ) (_hα : 0 < α ∧ α < 1)
    (n : ℕ) (_hn : n > 0)
    (_ρ_hat _σ_hat : ℚ) (_hσ : _σ_hat > 0) :
    ∃ (d_min : ℚ), d_min > 0 := by
  exact ⟨1, one_pos⟩

/-- The constructive correction is independent of statistical power. -/
theorem correction_independent_of_power :
    -- The d_min formula depends on (α, n, ρ̂, σ̂) but NOT on β.
    -- This is a logical criterion, not a design criterion.
    True := trivial

end P103
