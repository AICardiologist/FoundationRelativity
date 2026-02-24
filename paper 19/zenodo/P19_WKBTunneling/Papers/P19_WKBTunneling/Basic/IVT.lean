/-
Papers/P19_WKBTunneling/Basic/IVT.lean
Intermediate Value Theorem definitions and the IVT ↔ LLPO axiom.

The *approximate* IVT (for every ε > 0, there exists x with |f(x)| < ε) is
BISH-valid. The *exact* IVT (there exists x with f(x) = 0) is equivalent
to LLPO over BISH.

Design choice: we use plain ℝ → ℝ with a Continuous hypothesis rather than
bundled C(Set.Icc 0 1, ℝ) to avoid subtype coercion boilerplate throughout
the barrier files.
-/
import Papers.P19_WKBTunneling.Basic.LLPO
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Papers.P19

-- ========================================================================
-- Exact IVT (equivalent to LLPO)
-- ========================================================================

/-- Exact Intermediate Value Theorem on [0, 1].
    If f is continuous with f(0) < 0 < f(1), then there exists x ∈ [0,1]
    with f(x) = 0.

    This is equivalent to LLPO over BISH (Bridges-Richman 1987, Ishihara 1989). -/
def ExactIVT : Prop :=
  ∀ (f : ℝ → ℝ), Continuous f →
    f 0 < 0 → f 1 > 0 →
    ∃ x, 0 ≤ x ∧ x ≤ 1 ∧ f x = 0

-- ========================================================================
-- Approximate IVT (BISH-valid)
-- ========================================================================

/-- Approximate IVT on [0, 1]: BISH-valid, no omniscience needed.
    For every ε > 0, there exists x ∈ [0,1] with |f(x)| < ε.
    This is the constructive content of the IVT. -/
def ApproxIVT : Prop :=
  ∀ (f : ℝ → ℝ), Continuous f →
    f 0 < 0 → f 1 > 0 →
    ∀ ε : ℝ, ε > 0 → ∃ x, 0 ≤ x ∧ x ≤ 1 ∧ |f x| < ε

-- ========================================================================
-- Core axiom: ExactIVT ↔ LLPO
-- ========================================================================

/-- The Intermediate Value Theorem (exact root existence) is equivalent to
    LLPO over BISH.
    Reference: Bridges-Richman, "Varieties of Constructive Mathematics", 1987.
    Also: Ishihara, "Continuity and Nondiscontinuity in Constructive Mathematics", 1989.
    Also: Bridges-Vîță, "Techniques of Constructive Analysis", 2006, §4.3. -/
axiom exact_ivt_iff_llpo : ExactIVT ↔ LLPO

-- ========================================================================
-- Core axiom: BMC ↔ LPO
-- ========================================================================

/-- Bounded Monotone Convergence is equivalent to LPO over BISH.
    Reference: Bridges-Vîță, "Techniques of Constructive Analysis", 2006, Theorem 2.1.5.
    Re-declared locally (Paper 8 has the canonical formalization as lpo_iff_bmc). -/
axiom bmc_iff_lpo : BMC ↔ LPO

end Papers.P19
