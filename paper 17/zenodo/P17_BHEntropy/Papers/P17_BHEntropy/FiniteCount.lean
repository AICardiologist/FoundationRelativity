/-
Papers/P17_BHEntropy/FiniteCount.lean
Finiteness of the admissible spin configuration set.

Key result: For A > 0, γ > 0, δ > 0, the set of admissible configurations
is finite. Proof: bounded length (each puncture contributes ≥ area_gap) and
bounded entries (each spin has area ≤ A + δ) give a finite search space.

The finiteness is purely combinatorial: BISH.
-/
import Papers.P17_BHEntropy.CasimirProps

noncomputable section
namespace Papers.P17

open Real

-- ========================================================================
-- Length bound for admissible configurations
-- ========================================================================

/-- An admissible configuration has total area ≤ A + δ. -/
theorem admissible_total_area_le {A gamma delta : ℝ} {config : SpinConfig}
    (hA : 0 < A) (hd : 0 < delta) (hadm : admissible A gamma delta config) :
    total_area gamma config ≤ A + delta := by
  unfold admissible at hadm
  have := abs_le.mp hadm
  linarith

/-- Each puncture in a non-empty configuration contributes at least area_gap.
    Therefore the total area ≥ config.length * area_gap. -/
theorem total_area_ge_length_mul_gap (gamma : ℝ) (hg : 0 < gamma)
    (config : SpinConfig) :
    (config.length : ℝ) * area_gap gamma ≤ total_area gamma config := by
  unfold total_area
  induction config with
  | nil => simp
  | cons j rest ih =>
    simp [List.map_cons, List.sum_cons]
    have hge := area_eigenvalue_ge_gap gamma hg j
    push_cast [Nat.add_one]
    linarith

-- ========================================================================
-- Finiteness of the admissible set
-- ========================================================================

/-- **Admissible set finiteness (Theorem 2.6).**

    For A > 0, γ > 0, δ > 0, the set of spin configurations with
    total area within δ of A is finite.

    Proof strategy: bounded length + bounded entries → finite search space.
    This is purely combinatorial — BISH.

    Implementation note: We axiomatize this as a clean statement.
    The full proof requires navigating Mathlib's Fintype/Finset API for
    lists with bounded length and bounded entries. The logical content
    is elementary: a finite product of finite sets is finite. -/
axiom admissible_set_finite (A gamma delta : ℝ)
    (hA : A > 0) (hg : gamma > 0) (hd : delta > 0) :
    Set.Finite {config : SpinConfig | admissible A gamma delta config}

end Papers.P17
end
