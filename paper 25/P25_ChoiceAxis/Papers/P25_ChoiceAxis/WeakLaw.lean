/-
Papers/P25_ChoiceAxis/WeakLaw.lean
Paper 25: CC → Weak Law of Large Numbers

The weak law of large numbers (convergence in probability) calibrates
to Countable Choice:
  - CC provides the infinite sequence of independent measurements
  - Chebyshev's inequality provides the probability bound (BISH-valid)
  - The convergence Var(X)/(nε²) → 0 is constructive

Physical interpretation: "If we repeat a quantum measurement many times,
the statistics will approximately match the Born rule with high confidence."
This is the operational content of quantum mechanics as used in laboratories.
-/
import Papers.P25_ChoiceAxis.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.IdentDistrib

namespace Papers.P25_ChoiceAxis

open MeasureTheory Filter ProbabilityTheory Finset

/-! ## Statement of the Weak Law of Large Numbers -/

/-- **Weak Law of Large Numbers (convergence in probability).**
    For i.i.d. random variables with finite variance, the sample mean
    converges to the expected value in probability.

    Formally: for every ε > 0, P(|S_n/n − μ| ≥ ε) → 0 as n → ∞. -/
def WeakLLN : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (_hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (_hint : Integrable (X 0) μ)
    (_hvar : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    (_hindep : ∀ i j, i ≠ j → IndepFun (X i) (X j) μ),
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ {ω | ε ≤ |((∑ i ∈ Finset.range (n + 1), X i ω) /
        (↑(n + 1) : ℝ)) - ∫ x, X 0 x ∂μ|}) atTop (nhds 0)

/-! ## CC → Weak LLN -/

/-- **Countable Choice implies the Weak Law of Large Numbers.**

    The role of CC: the infinite sequence of independent measurements
    (X₀, X₁, X₂, ...) requires countable choice — we make one
    independent choice per trial. The choices are not dependent on
    each other, so CC (not DC) suffices.

    The probability bound uses Chebyshev's inequality:
      P(|S_n/n − μ| ≥ ε) ≤ Var(X) / (nε²)
    which tends to 0. Chebyshev's inequality is provable in BISH.

    **Proof strategy (in classical Lean):** The strong law gives a.e.
    convergence, and a.e. convergence implies convergence in probability
    for finite measures. The CC hypothesis marks the constructive content:
    the weak law needs only CC (not DC) because Chebyshev's inequality
    is constructive and the sequence of trials uses independent choices.

    **Calibration note:** This Lean proof routes through Mathlib's strong
    law (`strong_law_ae_real`), which is at DC level. This is a formalization
    shortcut — the strong law implies the weak law, so the proof is correct,
    but the logical strength used exceeds what is necessary. An independent
    CC-level proof exists via Chebyshev's inequality:
      P(|S_n/n − μ| ≥ ε) ≤ Var(X) / (nε²) → 0
    This route uses only variance bounds (constructive algebra) and does
    not require the Borel-Cantelli machinery or dependent refinement that
    make the strong law DC-level. The calibration claim (weak LLN ↔ CC)
    rests on the Chebyshev route, not on this Lean shortcut.

    **Key distinction from Strong LLN**: The weak law gives convergence
    in probability (a statement about the measure of exceptional sets
    shrinking), not almost-sure convergence (a statement about individual
    sequences). The former requires CC; the latter requires DC. -/
theorem weakLLN_of_cc : CC_N → WeakLLN := by
  intro _hcc
  -- In Lean's classical logic, the WLLN follows from the SLLN
  -- (a.e. convergence ⇒ convergence in probability for finite measures).
  -- The CC hypothesis makes the constructive dependency explicit:
  -- classically, DC ⊇ CC, so any CC-level result follows from the SLLN.
  intro Ω _ μ _ X hident hint _hvar hindep ε hε
  -- Convert pairwise independence to Mathlib's `Pairwise` form
  have hindep' : Pairwise fun i j => IndepFun (X i) (X j) μ :=
    fun i j hij => hindep i j hij
  -- Apply the strong law of large numbers from Mathlib
  have hslln := strong_law_ae_real X hint hindep' hident
  -- hslln : ∀ᵐ ω ∂μ, Tendsto (fun n => (∑ i ∈ range n, X i ω) / ↑n) atTop (nhds (∫ x, X 0 x ∂μ))
  -- Define the sample mean function for index shifting
  let f : ℕ → Ω → ℝ := fun n ω => (∑ i ∈ Finset.range n, X i ω) / ↑n
  -- The strong law gives a.e. convergence of f(n) → E[X₀]
  -- We need convergence of f(n+1) in probability (index shift)
  -- First, get a.e. convergence of f(n+1) → E[X₀]
  have hae : ∀ᵐ ω ∂μ, Tendsto (fun n => f (n + 1) ω) atTop (nhds (∫ x, X 0 x ∂μ)) := by
    filter_upwards [hslln] with ω hω
    exact hω.comp (tendsto_add_atTop_nat 1)
  -- Get AEStronglyMeasurable for each f(n+1)
  have hX_int : ∀ i, Integrable (X i) μ :=
    fun i => (hident i).symm.integrable_snd hint
  have hf_meas : ∀ n, AEStronglyMeasurable (fun ω => f (n + 1) ω) μ := by
    intro n
    show AEStronglyMeasurable (fun ω => (∑ i ∈ Finset.range (n + 1), X i ω) / ↑(n + 1)) μ
    exact ((integrable_finset_sum _ fun i _ => hX_int i).div_const _).aestronglyMeasurable
  -- Apply: a.e. convergence in finite measure ⇒ convergence in measure
  have him : TendstoInMeasure μ (fun n ω => f (n + 1) ω) atTop
      (fun _ => ∫ x, X 0 x ∂μ) :=
    tendstoInMeasure_of_tendsto_ae hf_meas hae
  -- Unpack TendstoInMeasure using the norm characterization
  rw [tendstoInMeasure_iff_norm] at him
  -- him : ∀ ε > 0, Tendsto (fun n => μ {x | ε ≤ ‖f(n+1)(x) - E[X₀]‖}) atTop (nhds 0)
  specialize him ε hε
  -- The set {x | ε ≤ ‖f(n+1)(x) - E[X₀]‖} equals {ω | ε ≤ |...|} since ‖r‖ = |r| for ℝ
  refine (tendsto_congr fun n => ?_).mp him
  simp only [f, Real.norm_eq_abs]

/-! ## Physical Interpretation

**Quantum measurement at the CC level:**

Consider a quantum system with observable A and state ρ.
Repeated measurement produces outcomes a₁, a₂, a₃, ...

The weak law says: for any tolerance ε and confidence δ,
there exists N such that after N measurements,

  P(|sample_mean − Tr(ρA)| > ε) < δ

This is what experimentalists actually verify: finite-sample statistics
match the Born rule prediction to within specified tolerance and confidence.

The countable choice principle CC enters because we need the infinite
sequence of measurement outcomes. Each measurement is an independent
choice from the outcome distribution — pure CC, not DC.

This is strictly weaker than the strong law (DC level), which claims
the sample mean converges for every individual sequence of outcomes
with probability 1. The strong law is an idealization; the weak law
is the operational content.
-/

end Papers.P25_ChoiceAxis
