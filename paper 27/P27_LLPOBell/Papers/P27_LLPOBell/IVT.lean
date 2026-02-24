/-
Papers/P27_LLPOBell/IVT.lean
Paper 27: The Logical Cost of Root-Finding
IVT.lean — Intermediate Value Theorem and the IVT ↔ LLPO equivalence

The *approximate* IVT (for every ε > 0, there exists x with |f(x)| < ε) is
BISH-valid (bisection converges without sign decisions). The *exact* IVT
(there exists x with f(x) = 0) is equivalent to LLPO over BISH.

Design choice: we use plain ℝ → ℝ with a Continuous hypothesis rather than
bundled C(Set.Icc 0 1, ℝ) to avoid subtype coercion boilerplate.
-/
import Papers.P27_LLPOBell.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Analysis.SpecificLimits.Basic

namespace Papers.P27

-- ========================================================================
-- Exact IVT (equivalent to LLPO)
-- ========================================================================

/-- Exact Intermediate Value Theorem on [0, 1].
    If f is continuous with f(0) < 0 < f(1), then there exists x ∈ [0,1]
    with f(x) = 0.

    This is equivalent to LLPO over BISH (Bridges-Richman 1987, Ishihara 1989).
    The claim f(0) < 0 and f(1) > 0 (strict) is standard — the ≤ version
    is derivable by perturbation. -/
def ExactIVT : Prop :=
  ∀ (f : ℝ → ℝ), Continuous f →
    f 0 < 0 → f 1 > 0 →
    ∃ x, 0 ≤ x ∧ x ≤ 1 ∧ f x = 0

-- ========================================================================
-- Approximate IVT (BISH-valid)
-- ========================================================================

/-- Approximate IVT on [0, 1]: BISH-valid, no omniscience needed.
    For every ε > 0, there exists x ∈ [0,1] with |f(x)| < ε.
    This is the constructive content of the IVT — bisection converges
    to an approximate root without requiring sign decisions. -/
def ApproxIVT : Prop :=
  ∀ (f : ℝ → ℝ), Continuous f →
    f 0 < 0 → f 1 > 0 →
    ∀ ε : ℝ, ε > 0 → ∃ x, 0 ≤ x ∧ x ≤ 1 ∧ |f x| < ε

-- ========================================================================
-- Core axiom: ExactIVT ↔ LLPO
-- ========================================================================

/-- The Intermediate Value Theorem (exact root existence) is equivalent to
    LLPO over BISH.

    Forward (IVT → LLPO): Given a binary sequence α with at most one 1,
    construct a continuous piecewise-linear function whose root position
    encodes whether the 1 is at an even or odd index. Apply IVT to get
    the root, then read off the even/odd decision.

    Backward (LLPO → IVT): Given LLPO and f continuous with f(0) < 0 < f(1),
    perform bisection. At each step, LLPO resolves the sign ambiguity when
    f(midpoint) is near zero (deciding f(c) ≤ 0 ∨ 0 ≤ f(c)).

    References:
    - Bridges-Richman, "Varieties of Constructive Mathematics", 1987, §3.3.
    - Ishihara, "Continuity and Nondiscontinuity in Constructive Mathematics",
      JSL 1989.
    - Bridges-Vîță, "Techniques of Constructive Analysis", 2006, §4.3. -/
axiom exact_ivt_iff_llpo : ExactIVT ↔ LLPO

-- ========================================================================
-- Derived helpers
-- ========================================================================

/-- ExactIVT follows from LLPO. -/
theorem exactIVT_of_LLPO (h : LLPO) : ExactIVT :=
  exact_ivt_iff_llpo.mpr h

/-- LLPO follows from ExactIVT. -/
theorem llpo_of_exactIVT (h : ExactIVT) : LLPO :=
  exact_ivt_iff_llpo.mp h

-- ========================================================================
-- LLPO for reals (sign decision)
-- ========================================================================

/-- LLPO implies real sign decision: for every x : ℝ, either x ≤ 0 or 0 ≤ x.

    This is a standard consequence of LLPO. The proof constructs a binary
    sequence from the Cauchy representation of x and applies LLPO.

    Reference: Ishihara, "Reverse Mathematics in Bishop's Constructive
    Mathematics", Philosophia Scientiae 2006, §3. -/
axiom llpo_real_sign : LLPO → ∀ (x : ℝ), x ≤ 0 ∨ 0 ≤ x

-- ========================================================================
-- Exact IVT implies Approximate IVT (trivially)
-- ========================================================================

/-- Exact IVT trivially implies Approximate IVT. -/
theorem exactIVT_implies_approxIVT : ExactIVT → ApproxIVT := by
  intro hivt f hcont hf0 hf1 ε hε
  obtain ⟨x, hx0, hx1, hfx⟩ := hivt f hcont hf0 hf1
  exact ⟨x, hx0, hx1, by rw [hfx]; simpa using hε⟩

-- ========================================================================
-- LLPO implies Approximate IVT (via Exact IVT)
-- ========================================================================

/-- LLPO implies Approximate IVT (trivially, via Exact IVT). -/
theorem llpo_implies_approxIVT : LLPO → ApproxIVT :=
  fun h => exactIVT_implies_approxIVT (exactIVT_of_LLPO h)

-- ========================================================================
-- Generalized IVT (arbitrary intervals)
-- ========================================================================

/-- Generalized ExactIVT on [a, b].
    If f is continuous with f(a) < 0 < f(b), then there exists c ∈ [a,b]
    with f(c) = 0. Derived from the [0,1] version by affine rescaling. -/
def GeneralizedIVT : Prop :=
  ∀ (f : ℝ → ℝ), Continuous f →
    ∀ (a b : ℝ), a < b → f a < 0 → 0 < f b →
      ∃ c, a ≤ c ∧ c ≤ b ∧ f c = 0

/-- ExactIVT on [0,1] implies the generalized version on [a,b].
    Proof: compose f with the affine map t ↦ a + t(b-a). -/
theorem exactIVT_implies_generalizedIVT : ExactIVT → GeneralizedIVT := by
  intro hivt f hcont a b hab hfa hfb
  -- g(t) = f(a + t * (b - a)) maps [0,1] to [a,b]
  let g : ℝ → ℝ := fun t => f (a + t * (b - a))
  have hg_cont : Continuous g := hcont.comp (continuous_const.add (continuous_id.mul continuous_const))
  have hg0 : g 0 < 0 := by simp [g, hfa]
  have hg1 : g 1 > 0 := by
    show f (a + 1 * (b - a)) > 0
    ring_nf
    linarith
  obtain ⟨t, ht0, ht1, hgt⟩ := hivt g hg_cont hg0 hg1
  refine ⟨a + t * (b - a), ?_, ?_, hgt⟩
  · linarith [mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ b - a)]
  · have : t * (b - a) ≤ 1 * (b - a) :=
      mul_le_mul_of_nonneg_right ht1 (by linarith)
    linarith

/-- LLPO implies Generalized IVT. -/
theorem llpo_implies_generalizedIVT : LLPO → GeneralizedIVT :=
  fun h => exactIVT_implies_generalizedIVT (exactIVT_of_LLPO h)

end Papers.P27
