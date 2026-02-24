/-
  Paper 31: The Physical Dispensability of Dependent Choice
  Defs.lean — Core definitions

  Part of the Constructive Reverse Mathematics Series (see Paper 10).

  Defines:
    - LPO (Limited Principle of Omniscience)
    - CC (Countable Choice)
    - DC (Dependent Choice)
    - EmpiricalPrediction (finite-time, finite-precision, bounded-error)
    - WLLN / SLLN (weak and strong law of large numbers)
    - MeanErgodic / Birkhoff (mean vs pointwise ergodic theorem)
    - TimeAverage (Cesàro mean of an orbit)

  The key insight of Paper 31: DC is needed only for the pointwise (ω-by-ω)
  infinite-time limit. All empirical predictions—finite time, finite precision,
  bounded error probability—are recoverable from BISH+LPO without DC.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Data.ENNReal.Basic

noncomputable section
namespace Papers.P31

open MeasureTheory Filter Topology Set

-- ========================================================================
-- Logical principles
-- ========================================================================

/-- Limited Principle of Omniscience.
    For every binary sequence, either all terms are false or some term is true. -/
def LPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ (∃ n, α n = true)

/-- Countable Choice: if for every n there exists an x satisfying P n x,
    then there exists a choice function.
    LPO implies CC over BISH. -/
def CC : Prop :=
  ∀ {α : Type} {P : ℕ → α → Prop}, (∀ n, ∃ x, P n x) → ∃ f : ℕ → α, ∀ n, P n (f n)

/-- Dependent Choice: given a total relation on a nonempty set,
    there exists an infinite chain.
    DC is strictly stronger than CC over BISH. -/
def DC : Prop :=
  ∀ {α : Type} {R : α → α → Prop},
    (∀ x, ∃ y, R x y) → ∀ x₀ : α, ∃ f : ℕ → α, f 0 = x₀ ∧ ∀ n, R (f n) (f (n + 1))

/-- LPO implies Countable Choice over BISH.
    (Ishihara 2006; see also Bridges–Vîță 2006, §2.2) -/
axiom cc_of_lpo : LPO → CC

-- ========================================================================
-- Empirical predictions (finite-time, finite-precision, bounded-error)
-- ========================================================================

/-- An empirical prediction is a statement of the form:
    "For sample size n ≥ N₀, the probability of deviation exceeding ε
     is less than δ."
    This is the universal form of all laboratory-verifiable claims. -/
structure EmpiricalBound (Ω : Type*) [MeasurableSpace Ω] where
  /-- The observable random variable at time/sample n -/
  observable : ℕ → Ω → ℝ
  /-- The predicted value -/
  target : ℝ
  /-- The probability measure -/
  P : Measure Ω
  /-- Measurement precision -/
  ε : ℝ
  /-- Confidence threshold -/
  δ : ℝ
  /-- Precision is positive -/
  hε : 0 < ε
  /-- Confidence threshold is positive -/
  hδ : 0 < δ

-- ========================================================================
-- Laws of Large Numbers
-- ========================================================================

/-- Weak Law of Large Numbers (WLLN).
    Convergence in probability: for every ε, δ > 0, there exists N₀ such that
    for all n ≥ N₀, P(|Sₙ/n − μ| ≥ ε) < δ.

    Cost: CC (constructing the sequence of approximants).
    Empirically: captures all finite-precision laboratory predictions. -/
def WLLN {Ω : Type*} [MeasurableSpace Ω] (S : ℕ → Ω → ℝ) (μ : ℝ) (P : Measure Ω) : Prop :=
  ∀ ε > (0 : ℝ), ∀ δ > (0 : ℝ), ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → 0 < n →
    P {ω | ε ≤ |S n ω / ↑n - μ|} < ENNReal.ofReal δ

/-- Strong Law of Large Numbers (SLLN).
    Almost-sure pointwise convergence: for P-almost every ω,
    Sₙ(ω)/n → μ as n → ∞.

    Cost: DC (tracking an individual trajectory ω for infinite time).
    Empirically: requires observing a single infinite trajectory. -/
def SLLN {Ω : Type*} [MeasurableSpace Ω] (S : ℕ → Ω → ℝ) (μ : ℝ) (P : Measure Ω) : Prop :=
  ∀ᵐ ω ∂P, Tendsto (fun n => S n ω / ↑n) atTop (𝓝 μ)

-- ========================================================================
-- Ergodic theory
-- ========================================================================

/-- Time average (Cesàro mean) of f along the orbit of T.
    A_N f(ω) = (1/N) · Σ_{k=0}^{N-1} f(T^k ω).
    Evaluates to 0 when N = 0 (division by zero gives 0 in Lean). -/
def TimeAverage {Ω : Type*} (T : Ω → Ω) (f : Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  (∑ k ∈ Finset.range N, f (T^[k] ω)) / ↑N

/-- Mean Ergodic Theorem (von Neumann).
    L² convergence: the ensemble-averaged squared deviation → 0.
    ∫ |A_N f − f̄|² dP → 0 as N → ∞.

    Cost: CC (constructing the L² projection f̄).
    Empirically: captures all macroscopic (ensemble-averaged) predictions. -/
def MeanErgodic {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω → Ω) (f f_bar : Ω → ℝ) (P : Measure Ω) : Prop :=
  Tendsto (fun N => ∫ ω, (TimeAverage T f N ω - f_bar ω)^2 ∂P) atTop (𝓝 0)

/-- Birkhoff Pointwise Ergodic Theorem.
    Almost-sure convergence: for P-a.e. ω, A_N f(ω) → f̄(ω).

    Cost: DC (tracking an individual trajectory for infinite time).
    Empirically: requires observing a single infinite orbit. -/
def Birkhoff {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω → Ω) (f f_bar : Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ᵐ ω ∂P, Tendsto (fun N => TimeAverage T f N ω) atTop (𝓝 (f_bar ω))

-- ========================================================================
-- The quantifier-swap characterization
-- ========================================================================

/-- Empirical topology: quantifiers outside the measure.
    ∀ ε, δ > 0, ∃ N₀, P({ω | error(N₀, ω) ≥ ε}) < δ.
    Cost: LPO + CC (extracting the modulus N₀ from a convergent sequence). -/
def EmpiricalConvergence {Ω : Type*} [MeasurableSpace Ω]
    (error : ℕ → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ ε > (0 : ℝ), ∀ δ > (0 : ℝ), ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
    P {ω | ε ≤ |error N ω|} < ENNReal.ofReal δ

/-- Ontological topology: quantifiers inside the measure.
    P({ω | ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, |error(N, ω)| < ε}) = 1.
    (Equivalently: a.e. pointwise convergence.)
    Cost: DC (the quantifier swap requires dependent choice). -/
def OntologicalConvergence {Ω : Type*} [MeasurableSpace Ω]
    (error : ℕ → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ᵐ ω ∂P, ∀ ε > (0 : ℝ), ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → |error N ω| < ε

end Papers.P31
end
