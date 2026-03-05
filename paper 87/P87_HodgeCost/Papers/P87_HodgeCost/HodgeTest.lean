/-
  Paper 87: The Omniscience Cost of the Hodge Condition
  The Uniform Hodge Test — Decision Problem Formulation

  The Hodge test asks: given a period matrix Ω ∈ H_g (Siegel upper half-space)
  presented as Cauchy sequences and a rational class α ∈ ∧^{2p} H¹(A, ℚ),
  is α of type (p,p)?

  This reduces to: for each off-diagonal (a,b) with a + b = 2p and a ≠ p,
  does the projection π_{a,b}(α) equal zero?

  Each projection is a ℚ-linear combination of period matrix entries (real numbers).
  Testing whether such a combination equals zero is a real-number equality test.

  Key insight (Bridges-Richman 1987): the statement ∀ x : ℝ, x = 0 ∨ x ≠ 0
  is exactly WLPO. Therefore, a uniform Hodge test decider implies WLPO.

  References:
  - Bridges-Richman, Varieties of Constructive Mathematics (1987), §1.3
  - Papers 72–74: DPT biconditional methodology
  - Shiga-Wolfart (1995): algebraic period entries ↔ CM type
-/

import Papers.P87_HodgeCost.CRMLevel
import Mathlib.Data.Real.Basic

namespace P87

open CRMLevel

/-! ## WLPO as real-number equality decision -/

/-- WLPO for real numbers: every real number is zero or nonzero. -/
def WLPO_Real : Prop := ∀ x : ℝ, x = 0 ∨ x ≠ 0

/-! ## Abstract analytic period matrix

  We axiomatise the period matrix as an abstract type. Concretely, this represents
  an element of the Siegel upper half-space H_g, whose entries are real numbers
  presented as Cauchy sequences. Mathlib does not have H_g, so we axiomatise
  the interface: a period matrix of genus g, and a projection function that
  extracts the real value of a Hodge projection.

  The projection hodge_projection Ω idx returns the real number π_{a,b}(α)
  for a fixed class α and the idx-th off-diagonal component. If this equals
  zero for all idx, then α is of type (p,p) — i.e., α is a Hodge class.
-/

/-- Abstract type of analytic period matrices of genus g. -/
axiom AnalyticPeriodMatrix (g : ℕ) : Type

/-- The Hodge projection: extracts the real value of the idx-th off-diagonal
    component π_{a,b}(α) for a fixed rational class α. -/
axiom hodge_projection {g : ℕ} (Ω : AnalyticPeriodMatrix g) (idx : ℕ) : ℝ

/-- A class is Hodge (type (p,p)) iff all off-diagonal projections vanish. -/
def is_hodge_analytic {g : ℕ} (Ω : AnalyticPeriodMatrix g) (idx : ℕ) : Prop :=
  hodge_projection Ω idx = 0

/-! ## The embedding reduction

  The key technique: given any real number x, we construct a period matrix Ω_x
  such that the Hodge projection recovers x. Concretely, start with a CM period
  matrix Ω₀ (algebraic entries) and perturb one entry by x. Choose the class α
  so the only non-trivial projection involves the perturbed entry.

  This is axiomatised as embed_real and embed_proj. The mathematical content:
  - embed_real x constructs Ω_x = Ω₀ + x · E_{jk} (perturbation of one entry)
  - embed_proj x proves that hodge_projection Ω_x 0 = x

  The construction is valid because:
  (1) H_g is an open subset of symmetric matrices, so small perturbations stay in H_g
  (2) The Hodge projection is continuous (hence the perturbed projection is close to x)
  (3) For the specific class α chosen, the projection IS exactly x (linearity)
-/

/-- Embed an arbitrary real number as a Hodge projection of a period matrix.
    Concretely: perturb a CM period matrix by x in one entry. -/
axiom embed_real (x : ℝ) : AnalyticPeriodMatrix 2

/-- The embedding recovers the original real number as the projection. -/
axiom embed_proj (x : ℝ) : hodge_projection (embed_real x) 0 = x

/-! ## Theorem B: A uniform Hodge decider implies WLPO

  If there exists an algorithm that decides, for ANY period matrix Ω and
  ANY projection index, whether the Hodge projection vanishes, then WLPO holds.

  Proof: given x ∈ ℝ, apply the decider to (embed_real x, 0). The decider
  returns either "hodge_projection (embed_real x) 0 = 0" or its negation.
  By embed_proj, this is equivalent to "x = 0" or "x ≠ 0". This is WLPO.
-/

theorem uniform_hodge_test_implies_wlpo
    (decider : ∀ (g : ℕ) (Ω : AnalyticPeriodMatrix g) (idx : ℕ),
      Decidable (is_hodge_analytic Ω idx)) :
    WLPO_Real := by
  intro x
  -- Apply the decider to the embedded period matrix
  cases decider 2 (embed_real x) 0 with
  | isTrue h =>
    -- h : hodge_projection (embed_real x) 0 = 0
    -- By embed_proj: hodge_projection (embed_real x) 0 = x
    -- Therefore x = 0
    left
    rw [← embed_proj x]
    exact h
  | isFalse h =>
    -- h : ¬ (hodge_projection (embed_real x) 0 = 0)
    -- By embed_proj: hodge_projection (embed_real x) 0 = x
    -- Therefore x ≠ 0
    right
    intro hx
    apply h
    rw [← embed_proj x] at hx
    exact hx

/-! ## Converse: WLPO implies the uniform Hodge test is decidable

  In the other direction, if WLPO holds, then for any period matrix Ω and
  projection index idx, the Hodge projection test is decidable: we can decide
  whether any real number equals zero.
-/

theorem wlpo_implies_uniform_hodge_decidable
    (wlpo : WLPO_Real) :
    ∀ (g : ℕ) (Ω : AnalyticPeriodMatrix g) (idx : ℕ),
      (is_hodge_analytic Ω idx) ∨ ¬(is_hodge_analytic Ω idx) := by
  intro g Ω idx
  exact wlpo (hodge_projection Ω idx)

/-! ## Equivalence: Uniform Hodge decidability ↔ WLPO -/

theorem uniform_hodge_iff_wlpo :
    (∀ (g : ℕ) (Ω : AnalyticPeriodMatrix g) (idx : ℕ),
      (is_hodge_analytic Ω idx) ∨ ¬(is_hodge_analytic Ω idx))
    ↔ WLPO_Real := by
  constructor
  · -- Forward: decidability → WLPO
    intro h x
    have := h 2 (embed_real x) 0
    unfold is_hodge_analytic at this
    rw [embed_proj] at this
    exact this
  · -- Reverse: WLPO → decidability
    exact wlpo_implies_uniform_hodge_decidable

end P87
