/-
  Paper 51: The Constructive Archimedean Rescue in BSD
  HeightBounds.lean — Silverman's height difference bound and consequences

  The central BISH engine: Silverman's theorem gives
    |ĥ(P) − ½h(P)| ≤ μ(E)
  from which we derive:
    ĥ(P) ≤ C  ⟹  h(P) ≤ 2C + 2μ(E)

  This is the key step converting an analytic bound (on the canonical
  height) into an arithmetic bound (on the naive height), which then
  gives a finite search space.

  The positive-definiteness of ĥ (the Archimedean property, u = 1)
  ensures that C > 0 for non-torsion points, making the bound
  non-trivial. Without positive-definiteness (p-adic case, u = 4),
  C could be 0 for non-torsion points, and the bound collapses.

  Zero `sorry`s. Zero custom axioms.
-/
import Papers.P51_BSD.Defs

namespace Papers.P51

-- ========================================================================
-- Silverman's Height Difference Bound
-- ========================================================================

/-- Silverman's Theorem (AEC, Theorem VIII.9.3):
    For an elliptic curve E/ℚ, there exists a computable constant μ(E)
    such that for all P ∈ E(ℚ):
      |ĥ(P) − ½·h(P)| ≤ μ(E)

    We define this as a Prop-valued predicate relating an ECData
    (which carries μ) and a canonical height function. The canonical
    height is axiomatized (its construction requires Mordell-Weil),
    but the bound is a concrete real-analysis statement. -/
def SilvermanBound (E : ECData) (canonicalHeight : RatPoint → ℝ) : Prop :=
  ∀ P : RatPoint, |canonicalHeight P - (1 / 2) * naiveHeight P| ≤ E.mu

-- ========================================================================
-- Key Consequence: Canonical height bounds naive height (BISH core)
-- ========================================================================

/-- **BISH Core.** From Silverman's bound, a canonical height bound
    implies a naive height bound:
      ĥ(P) ≤ C  ⟹  h(P) ≤ 2C + 2μ(E)

    Proof: From |ĥ(P) − ½h(P)| ≤ μ(E):
      ĥ(P) − ½h(P) ≥ −μ(E)
      ½h(P) ≤ ĥ(P) + μ(E) ≤ C + μ(E)
      h(P) ≤ 2C + 2μ(E)

    This uses only `abs_le` decomposition and `linarith`.
    No omniscience principle. No Fan Theorem. Pure BISH. -/
theorem naiveHeight_bounded_of_canonical
    (E : ECData) (canonicalHeight : RatPoint → ℝ)
    (hS : SilvermanBound E canonicalHeight)
    (P : RatPoint) (C : ℝ) (hC : canonicalHeight P ≤ C) :
    naiveHeight P ≤ 2 * C + 2 * E.mu := by
  have hsb := hS P
  rw [abs_le] at hsb
  -- hsb.1 : -(E.mu) ≤ canonicalHeight P - 1/2 * naiveHeight P
  -- hsb.2 : canonicalHeight P - 1/2 * naiveHeight P ≤ E.mu
  -- From hsb.1: 1/2 * naiveHeight P ≤ canonicalHeight P + E.mu ≤ C + E.mu
  -- Therefore: naiveHeight P ≤ 2 * (C + E.mu) = 2*C + 2*E.mu
  linarith [hsb.1]

-- ========================================================================
-- Positive-Definiteness of the Canonical Height
-- ========================================================================

/-- The canonical height is positive-definite on non-torsion points.
    This is the Archimedean property (u = 1 in the Néron-Tate pairing):
      ĥ(P) > 0 for all non-torsion P ∈ E(ℚ).

    This is the property that makes the BSD search constructive.
    Over ℚ_p (u = 4), the p-adic canonical height ĥ_p can be zero
    for non-torsion points — positive-definiteness fails, and the
    MP → BISH conversion breaks down (exceptional zero pathology). -/
def PositiveDefinite (canonicalHeight : RatPoint → ℝ)
    (isTorsion : RatPoint → Prop) : Prop :=
  ∀ P : RatPoint, ¬isTorsion P → 0 < canonicalHeight P

-- ========================================================================
-- The Silverman mu formula (computable from curve data)
-- ========================================================================

/-- Silverman's explicit formula for μ(E).
      μ(E) = ⅛·log|j(E)| + 1/12·log|Δ_min| + 0.973

    This establishes that μ is a deterministic, computable function
    of the curve invariants — no search required. The constant 0.973
    is from Silverman's original paper; we use 973/1000 as the
    rational approximation. -/
def SilvermanMuFormula (E : ECData) : Prop :=
  E.mu = (1 / 8) * |E.log_j| + (1 / 12) * |E.log_Delta| + 973 / 1000

-- ========================================================================
-- Monotonicity of the height bound
-- ========================================================================

/-- The height bound is monotone in C: a larger canonical height bound
    gives a larger (weaker) naive height bound. -/
theorem height_bound_monotone (E : ECData) (C₁ C₂ : ℝ) (h : C₁ ≤ C₂) :
    2 * C₁ + 2 * E.mu ≤ 2 * C₂ + 2 * E.mu := by
  linarith

-- ========================================================================
-- The height bound is non-negative when C ≥ 0
-- ========================================================================

/-- When the canonical height bound C is non-negative, so is the
    naive height bound 2C + 2μ. -/
theorem height_bound_nonneg (E : ECData) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ 2 * C + 2 * E.mu := by
  linarith [E.hmu]

end Papers.P51
