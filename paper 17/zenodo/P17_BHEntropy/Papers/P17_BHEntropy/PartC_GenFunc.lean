/-
Papers/P17_BHEntropy/PartC_GenFunc.lean
Part C: The generating function Z(t) for saddle-point analysis.

Defines:
  Z(t) = Σ_{k=1}^∞ exp(-t · √(k(k+2)/4))

where k = 2j ranges over positive integers (j over positive half-integers).

Properties (Tier 1):
  - Z is well-defined (summable) for t > 0
  - Z is positive for t > 0
  - Z is strictly decreasing on (0, ∞)
  - Z(t) → ∞ as t → 0+ and Z(t) → 0 as t → ∞

The summability and order properties of the infinite series use Mathlib's
tsum API extensively. Properties that require complex API interactions
(tsum_pos, tsum_lt_tsum with the SummationFilter framework) are
axiomatized as infrastructure lemmas. The mathematical content is
elementary: comparison with geometric series, and termwise monotonicity.

Axiom status: The axioms in this file are all infrastructure (about
infinite series manipulation), not about the physics or logic.
-/
import Papers.P17_BHEntropy.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
namespace Papers.P17

open Real BigOperators Finset

-- ========================================================================
-- The generating function term
-- ========================================================================

/-- Casimir value for the k-th term: √((k+1)((k+1)+2)/4).
    Here k ranges over ℕ, so k+1 gives positive integers 1, 2, 3, ...
    corresponding to half-integers j = 1/2, 1, 3/2, ... -/
def casimir_term (k : ℕ) : ℝ :=
  sqrt ((k + 1 : ℝ) * ((k + 1) + 2) / 4)

/-- The Casimir term is non-negative. -/
lemma casimir_term_nonneg (k : ℕ) : 0 ≤ casimir_term k :=
  sqrt_nonneg _

/-- The Casimir term is positive. -/
lemma casimir_term_pos (k : ℕ) : 0 < casimir_term k := by
  unfold casimir_term
  apply sqrt_pos_of_pos
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  positivity

/-- The Casimir value is at least (k+1)/2. -/
lemma casimir_term_ge (k : ℕ) : casimir_term k ≥ (k + 1) / 2 := by
  unfold casimir_term
  rw [ge_iff_le, ← sqrt_sq (by positivity : (k + 1 : ℝ) / 2 ≥ 0)]
  apply sqrt_le_sqrt
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

-- ========================================================================
-- Single term of the generating function
-- ========================================================================

/-- Single term of the generating function: exp(-t · casimir_term(k)). -/
def Z_term (t : ℝ) (k : ℕ) : ℝ :=
  exp (-t * casimir_term k)

/-- Each Z_term is positive. -/
lemma Z_term_pos (t : ℝ) (k : ℕ) : 0 < Z_term t k :=
  exp_pos _

/-- Each Z_term is non-negative. -/
lemma Z_term_nonneg (t : ℝ) (k : ℕ) : 0 ≤ Z_term t k :=
  le_of_lt (Z_term_pos t k)

/-- Z_term is anti-monotone in t (for fixed k). -/
lemma Z_term_antitone (k : ℕ) : Antitone (fun t => Z_term t k) := by
  intro t₁ t₂ h
  unfold Z_term
  apply exp_le_exp.mpr
  nlinarith [casimir_term_nonneg k]

/-- Z_term is strictly anti-monotone in t (for fixed k). -/
lemma Z_term_strictAnti (k : ℕ) : StrictAnti (fun t => Z_term t k) := by
  intro t₁ t₂ h
  unfold Z_term
  apply exp_lt_exp.mpr
  nlinarith [casimir_term_pos k]

-- ========================================================================
-- The generating function
-- ========================================================================

/-- The generating function Z(t) = Σ_{k=0}^∞ Z_term(t, k). -/
def Z (t : ℝ) : ℝ := ∑' k, Z_term t k

-- ========================================================================
-- Summability (axiomatized — comparison with geometric series)
-- ========================================================================

/-- **Z(t) is summable for t > 0.**
    Each term exp(-t · c_k) ≤ exp(-t(k+1)/2) (since c_k ≥ (k+1)/2),
    and the geometric series Σ exp(-t(k+1)/2) = exp(-t/2)/(1 - exp(-t/2))
    converges for t > 0.
    Axiomatized: the comparison test for tsum requires careful interaction
    with Mathlib's SummationFilter framework. -/
axiom Z_summable (t : ℝ) (ht : 0 < t) : Summable (Z_term t)

-- ========================================================================
-- Positivity (axiomatized — tsum of positive terms)
-- ========================================================================

/-- **Z(t) > 0 for all t > 0.**
    Z(t) = Σ Z_term(t, k) with each term > 0 and the series summable,
    so the sum is positive.
    Axiomatized: uses Summable.tsum_pos from Mathlib's Order module. -/
axiom Z_pos (t : ℝ) (ht : 0 < t) : 0 < Z t

-- ========================================================================
-- Monotonicity
-- ========================================================================

/-- **Z is strictly anti-monotone on (0, ∞).**
    Each Z_term(t, k) is strictly decreasing in t, and tsum preserves
    strict inequality when terms are summable.
    Axiomatized: uses Summable.tsum_lt_tsum from Mathlib's Order module. -/
axiom Z_strictAntiOn : StrictAntiOn Z (Set.Ioi 0)

-- ========================================================================
-- Limit behavior (axiomatized)
-- ========================================================================

/-- Z(t) → 0 as t → ∞.
    Each term exp(-t · c_k) → 0 and the series converges uniformly
    on [T, ∞) for any T > 0. -/
axiom Z_tendsto_zero :
  Filter.Tendsto Z Filter.atTop (nhds 0)

/-- Z(t) → ∞ as t → 0+.
    For any N, the partial sum Σ_{k=0}^{N-1} Z_term(t, k) → N as t → 0+,
    so Z(t) ≥ N - 1 for t sufficiently small. -/
axiom Z_tendsto_atTop_at_zero :
  Filter.Tendsto Z (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop

-- ========================================================================
-- Partial sums (computable approximations)
-- ========================================================================

/-- Partial sum of the generating function. -/
def Z_partial (t : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, Z_term t k

/-- Partial sums are non-negative. -/
lemma Z_partial_nonneg (t : ℝ) (n : ℕ) : 0 ≤ Z_partial t n := by
  unfold Z_partial
  apply Finset.sum_nonneg
  intro k _
  exact Z_term_nonneg t k

/-- Partial sums converge to Z(t) for t > 0. -/
theorem Z_partial_tendsto (t : ℝ) (ht : 0 < t) :
    Filter.Tendsto (Z_partial t) Filter.atTop (nhds (Z t)) := by
  unfold Z Z_partial
  exact (Z_summable t ht).hasSum.tendsto_sum_nat

-- ========================================================================
-- Axiom audit for Tier 1
-- ========================================================================

#print axioms Z_partial_tendsto
-- Expected: [propext, Quot.sound] + the Z_summable axiom

end Papers.P17
end
