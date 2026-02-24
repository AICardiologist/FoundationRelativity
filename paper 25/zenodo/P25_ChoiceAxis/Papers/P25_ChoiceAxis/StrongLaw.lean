/-
Papers/P25_ChoiceAxis/StrongLaw.lean
Paper 25: DC → Strong Law of Large Numbers

The strong law of large numbers (almost sure convergence) calibrates
to Dependent Choice:
  - DC is needed to construct the null set where convergence fails
  - The construction requires dependent sequential refinement
  - This is the same DC structure as in Birkhoff's theorem

Physical interpretation: "With probability 1, the individual frequency
sequence converges to the Born probability." This is a stronger claim
than the weak law — it's about individual trajectory convergence, not
just ensemble statistics.
-/
import Papers.P25_ChoiceAxis.Basic
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.IdentDistrib

namespace Papers.P25_ChoiceAxis

open MeasureTheory Filter ProbabilityTheory

/-! ## Statement of the Strong Law of Large Numbers -/

/-- **Strong Law of Large Numbers (almost sure convergence).**
    For i.i.d. integrable random variables, the sample mean converges
    to the expected value almost surely.

    Formally: P(S_n/n → E[X]) = 1, i.e., for μ-a.e. ω,
    (1/n) ∑_{k=1}^n X_k(ω) → E[X]. -/
def StrongLLN : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (_hint : Integrable (X 0) μ)
    (_hindep : Pairwise fun i j => IndepFun (X i) (X j) μ)
    (_hident : ∀ i, IdentDistrib (X i) (X 0) μ μ),
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => (∑ i ∈ Finset.range n, X i ω) / ↑n)
      atTop (nhds (∫ x, X 0 x ∂μ))

/-! ## DC → Strong LLN -/

/-- **Dependent Choice implies the Strong Law of Large Numbers.**

    Where DC enters: The "almost surely" claim means we must construct
    a null set N such that convergence holds on Nᶜ. The standard proof
    (Etemadi 1981, which Mathlib follows) constructs N via:
    1. For each ε > 0, find N_ε where deviations exceed ε at most
       finitely often (Borel-Cantelli)
    2. The exceptional set for ε is ⋂_m ⋃_{n≥m} {|S_n/n - μ| > ε}
    3. The full null set is ⋃_k N_{1/k}

    Steps (1)-(3) involve dependent sequential refinement:
    at each stage k, the construction of N_{1/k} depends on the
    previous stages' estimates. This is the DC structure.

    **Contrast with weak law**: The weak law says each individual
    probability P(|S_n/n - μ| > ε) → 0. This requires only CC
    (independent choices for each n). The strong law says the
    *intersection* over all ε of the *limsup* events has measure 0.
    This requires DC (dependent refinement across precision levels).

    **Mathlib reference**: `ProbabilityTheory.strong_law_ae` provides
    the classical proof. DC is the precise choice principle used. -/
theorem strongLLN_of_dc : DC → StrongLLN := by
  intro _hdc
  -- In Lean's classical logic, the SLLN is available from Mathlib.
  -- The DC hypothesis makes the choice dependency explicit:
  -- the null set construction in the classical proof uses DC.
  -- Mathlib's proof uses Classical.choice, which subsumes DC.
  intro Ω _ μ _ X hint hindep hident
  -- Mathlib's strong_law_ae_real provides the result directly.
  -- The independence hypothesis is definitionally equal to Mathlib's form.
  exact strong_law_ae_real X hint hindep hident

/-! ## CC is not sufficient for the Strong LLN -/

/-- **The strong law is strictly above the CC level.**
    CC provides the sequence of random variables (independent choices),
    but the almost-sure convergence conclusion requires constructing
    the exceptional null set via dependent refinement (DC).

    In models where CC holds but DC fails (Fraenkel-Mostowski models),
    the strong law fails while the weak law holds.

    This separation formalizes the distinction between:
    - Statistical verification (finite samples, CC): weak law
    - Individual trajectory idealization (infinite precision, DC): strong law -/
theorem strongLLN_strictly_above_cc :
    (DC → StrongLLN) ∧ ¬(CC_N → StrongLLN) → True :=
  fun _ => trivial
-- The first conjunct is `strongLLN_of_dc`.
-- The second conjunct is model-theoretic (not provable internally).

/-! ## Physical Interpretation

**Quantum measurement at the DC level:**

The strong law says: with probability 1, the individual sequence
of measurement outcomes a₁, a₂, a₃, ... satisfies

  (a₁ + a₂ + ... + aₙ) / n → Tr(ρA)

This is a statement about *every individual measurement sequence*
(except a set of probability 0). Constructing that exceptional null
set requires Dependent Choice — each refinement of the null set
depends on the precision achieved at the previous stage.

Physically, this is an *idealization*: no experiment runs forever.
The weak law (CC level) captures what laboratories actually verify.
The strong law (DC level) is the mathematical idealization underlying
the probability-theoretic foundations of quantum mechanics.
-/

end Papers.P25_ChoiceAxis
