/-
  Paper 30: The Physical Dispensability of the Fan Theorem
  Defs.lean — Core definitions

  Part of the Constructive Reverse Mathematics Series (see Paper 10).

  Defines:
    - LPO (Limited Principle of Omniscience)
    - BMC (Bounded Monotone Convergence)
    - ExactEVT (exact attainment on [a,b])
    - ApproxEVT (supremum + ε-attainment on [a,b])
    - EVT_max (exact attainment on [0,1], a.k.a. Fan Theorem)
    - FanTheorem := EVT_max
    - Grid infrastructure (gridPoint, gridMaxVal, runningGridMax)
    - Rescaling infrastructure (rescale, unscale)

  The key insight of Paper 30: ApproxEVT requires only BMC ≡ LPO,
  while ExactEVT requires the full Fan Theorem. Since no finite-precision
  experiment can distinguish exact from ε-approximate optimization,
  FT is physically dispensable.
-/
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Finset.Max

noncomputable section
namespace Papers.P30

open Set Real

-- ========================================================================
-- Logical principles
-- ========================================================================

/-- Limited Principle of Omniscience.
    For every binary sequence, either all terms are false or some term is true. -/
def LPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ (∃ n, α n = true)

/-- Bounded Monotone Convergence: every bounded non-decreasing sequence
    of reals has a limit. Equivalent to LPO over BISH [Bridges–Vîță 2006]. -/
def BMC : Prop :=
  ∀ (a : ℕ → ℝ) (M : ℝ),
    Monotone a →
    (∀ n, a n ≤ M) →
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |a N - L| < ε

/-- BMC follows from LPO. Bridges–Vîță 2006, Theorem 2.1.5. -/
axiom bmc_of_lpo : LPO → BMC

-- ========================================================================
-- Extreme Value Theorems
-- ========================================================================

/-- Exact EVT: every continuous function on [a,b] attains its supremum.
    This is the assertion that requires the Fan Theorem. -/
def ExactEVT : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a < b → ContinuousOn f (Icc a b) →
    ∃ x ∈ Icc a b, ∀ y ∈ Icc a b, f y ≤ f x

/-- Approximate EVT: the supremum exists and is ε-attainable.
    This is the assertion that requires only BMC ≡ LPO. -/
def ApproxEVT : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a < b → ContinuousOn f (Icc a b) →
    ∃ S : ℝ, (∀ y ∈ Icc a b, f y ≤ S) ∧
      ∀ ε : ℝ, 0 < ε → ∃ x ∈ Icc a b, S - ε < f x

/-- EVT_max on [0,1]: every continuous function on [0,1] attains its maximum.
    Equivalent to the Fan Theorem (Berger 2005, Bridges–Vîță 2006). -/
def EVT_max : Prop :=
  ∀ (f : ℝ → ℝ), ContinuousOn f (Icc 0 1) →
    ∃ x ∈ Icc (0 : ℝ) (1 : ℝ), ∀ y ∈ Icc (0 : ℝ) (1 : ℝ), f y ≤ f x

/-- The Fan Theorem, defined via its EVT equivalent. -/
def FanTheorem : Prop := EVT_max

-- ========================================================================
-- Grid infrastructure
-- ========================================================================

/-- Grid point: the k-th point of an n-point uniform grid on [a,b].
    gridPoint a b n k = a + k · (b − a) / n. -/
def gridPoint (a b : ℝ) (n : ℕ) (k : ℕ) : ℝ :=
  a + ↑k * (b - a) / ↑n

/-- The maximum value of f on the n-point grid (grid points 0, 1, ..., n).
    Uses Finset.max' which requires the set to be nonempty. -/
def gridMaxVal (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  ((Finset.range (n + 1)).image (fun k => f (gridPoint a b (n + 1) k))).max'
    ⟨f (gridPoint a b (n + 1) 0),
     Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n), rfl⟩⟩

/-- Running maximum of grid max values.
    runningGridMax f a b n = max(gridMaxVal f a b 0, ..., gridMaxVal f a b n).
    This is monotone (non-decreasing) by construction. -/
def runningGridMax (f : ℝ → ℝ) (a b : ℝ) : ℕ → ℝ
  | 0 => gridMaxVal f a b 0
  | n + 1 => max (runningGridMax f a b n) (gridMaxVal f a b (n + 1))

-- ========================================================================
-- Rescaling infrastructure
-- ========================================================================

/-- Affine map sending [0,1] to [a,b]: t ↦ a + t·(b − a). -/
def rescale (a b : ℝ) (t : ℝ) : ℝ := a + t * (b - a)

/-- Inverse rescaling: x ↦ (x − a) / (b − a), sending [a,b] to [0,1]. -/
def unscale (a b : ℝ) (x : ℝ) : ℝ := (x - a) / (b - a)

end Papers.P30
end
