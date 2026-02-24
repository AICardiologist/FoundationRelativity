/-
Papers/P19_WKBTunneling/WKB/Action.lean
WKB action integral: S = ∫_{x₁}^{x₂} √(2m(V(x) - E)) dx

The action integral is defined via Mathlib's intervalIntegral. The integrand
is continuous (hence integrable) on the compact interval [x₁, x₂].
-/
import Papers.P19_WKBTunneling.Barrier.Definitions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
namespace Papers.P19

-- ========================================================================
-- WKB action integral
-- ========================================================================

/-- The WKB integrand: √(2m(V(x) - E)).
    Nonneg in the classically forbidden region where V(x) ≥ E. -/
def wkbIntegrand (V : ℝ → ℝ) (E m : ℝ) (x : ℝ) : ℝ :=
  Real.sqrt (2 * m * (V x - E))

/-- The WKB integrand is always nonneg (sqrt is nonneg by definition). -/
lemma wkbIntegrand_nonneg (V : ℝ → ℝ) (E m x : ℝ) :
    0 ≤ wkbIntegrand V E m x :=
  Real.sqrt_nonneg _

/-- WKB action integral through the barrier.
    S = ∫_{x₁}^{x₂} √(2m(V(x) - E)) dx -/
def wkbAction (B : Barrier) (tp : TurningPoints B) (m : ℝ) : ℝ :=
  ∫ x in tp.x₁..tp.x₂, wkbIntegrand B.V B.E m x

/-- Alternative form: action integral for a specific barrier with
    explicitly given turning points. -/
def wkbActionExplicit (V : ℝ → ℝ) (E m x₁ x₂ : ℝ) : ℝ :=
  ∫ x in x₁..x₂, Real.sqrt (2 * m * (V x - E))

-- ========================================================================
-- Basic properties
-- ========================================================================

/-- The WKB action is the integral of the integrand. (Definitional unfolding.) -/
lemma wkbAction_eq (B : Barrier) (tp : TurningPoints B) (m : ℝ) :
    wkbAction B tp m = ∫ x in tp.x₁..tp.x₂, Real.sqrt (2 * m * (B.V x - B.E)) :=
  rfl

end Papers.P19
end
