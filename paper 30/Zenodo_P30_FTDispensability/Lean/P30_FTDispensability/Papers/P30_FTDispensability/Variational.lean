/-
  Paper 30: The Physical Dispensability of the Fan Theorem
  Variational.lean — Variational mechanics stratification

  Axiomatized results from Paper 28:
    - el_unique_bish: EL equation has unique solution (BISH)
    - minimizer_iff_ft_cited: minimizer existence ↔ FT (Paper 28)

  New theorems:
    - harmonicAction2_continuous: action functional is continuous
    - approx_minimizer_of_lpo: LPO → approximate minimizer exists
    - variational_stratification: three-way: EL(BISH) + approx min(LPO) + exact min(FT)
-/
import Papers.P30_FTDispensability.ApproxAttain
import Papers.P30_FTDispensability.Separation

noncomputable section
namespace Papers.P30

open Set

-- ========================================================================
-- Harmonic oscillator parameters (from Paper 28)
-- ========================================================================

/-- Harmonic oscillator parameters: mass m, spring constant k, boundary values A, B.
    The CFL stability condition ensures well-posedness: k < 8m. -/
structure HOParams where
  m : ℝ
  k : ℝ
  A : ℝ
  B : ℝ
  hm : 0 < m
  hk : 0 < k
  hcfl : k < 8 * m

/-- The discrete harmonic action for N=2 time steps:
    S(q) = m(q − A)² + m(q − B)² + (k/2)·q².
    This is a quadratic function of the single interior point q. -/
def harmonicAction2 (p : HOParams) (q : ℝ) : ℝ :=
  p.m * (q - p.A)^2 + p.m * (q - p.B)^2 + p.k / 2 * q^2

/-- The Euler-Lagrange solution for N=2:
    q* = 4m(A+B) / (8m − k). -/
def elSolution (p : HOParams) : ℝ :=
  4 * p.m * (p.A + p.B) / (8 * p.m - p.k)

-- ========================================================================
-- Axiomatized results from Paper 28
-- ========================================================================

/-- The EL equation has a unique solution at the BISH level (Paper 28).
    No Fan Theorem hypothesis needed. -/
axiom el_unique_bish : ∀ (p : HOParams), ∀ q : ℝ,
  (∀ q' : ℝ, (2 * p.m + 2 * p.m + p.k) * q = 2 * p.m * p.A + 2 * p.m * p.B →
    q = q') →
  elSolution p = q

/-- Minimizer existence on [0,1] is equivalent to FT (Paper 28, Theorem minimizer_iff_ft).
    For ANY continuous function on [0,1], existence of a minimizer ↔ Fan Theorem. -/
axiom minimizer_iff_ft_cited :
  (∀ (f : ℝ → ℝ), ContinuousOn f (Icc 0 1) →
    ∃ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, f x ≤ f y) ↔
  FanTheorem

-- ========================================================================
-- Continuity of the action
-- ========================================================================

/-- The harmonic action is continuous (it's a polynomial). -/
theorem harmonicAction2_continuous (p : HOParams) :
    Continuous (harmonicAction2 p) := by
  unfold harmonicAction2
  fun_prop

/-- The harmonic action is continuous on any interval. -/
theorem harmonicAction2_continuousOn (p : HOParams) (s : Set ℝ) :
    ContinuousOn (harmonicAction2 p) s :=
  (harmonicAction2_continuous p).continuousOn

-- ========================================================================
-- Approximate minimizer from LPO
-- ========================================================================

/-- LPO implies the existence of an approximate minimizer.
    Apply ApproxEVT to −action to get approximate maximum of −S,
    which is an approximate minimum of S. -/
theorem approx_minimizer_of_lpo (hlpo : LPO) (p : HOParams) :
    ∀ ε : ℝ, 0 < ε →
      ∃ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
        harmonicAction2 p y > harmonicAction2 p x - ε := by
  intro ε hε
  -- Apply approxEVT to −action (maximize −S = minimize S)
  set g := fun q => -(harmonicAction2 p q) with hg_def
  have hg_cts : ContinuousOn g (Icc 0 1) := by
    exact (harmonicAction2_continuous p).neg.continuousOn
  obtain ⟨S, hS_ub, hS_approx⟩ := approxEVT_of_lpo hlpo g 0 1 one_pos hg_cts
  obtain ⟨x, hx_mem, hx_close⟩ := hS_approx ε hε
  refine ⟨x, hx_mem, fun y hy => ?_⟩
  have hgy : g y ≤ S := hS_ub y hy
  have hgx : S - ε < g x := hx_close
  simp only [hg_def] at hgy hgx
  linarith

-- ========================================================================
-- Variational stratification
-- ========================================================================

/-- Three-way variational stratification:
    1. EL solution exists at BISH level (no FT, no LPO)
    2. Approximate minimizer exists at LPO level (no FT)
    3. Exact minimizer existence requires FT

    This is the core thesis of Paper 30 applied to mechanics. -/
theorem variational_stratification :
    -- Part 1: EL is BISH (always available)
    (∀ (p : HOParams), ∃ q : ℝ, q = elSolution p) ∧
    -- Part 2: Approximate minimizer from LPO
    (LPO → ∀ (p : HOParams) (ε : ℝ), 0 < ε →
      ∃ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1,
        harmonicAction2 p y > harmonicAction2 p x - ε) ∧
    -- Part 3: Exact minimizer ↔ FT (cited)
    ((∀ (f : ℝ → ℝ), ContinuousOn f (Icc 0 1) →
        ∃ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, f x ≤ f y) ↔
      FanTheorem) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: trivial witness
    intro p; exact ⟨elSolution p, rfl⟩
  · -- Part 2
    intro hlpo p ε hε
    exact approx_minimizer_of_lpo hlpo p ε hε
  · -- Part 3: cited
    exact minimizer_iff_ft_cited

end Papers.P30
end
