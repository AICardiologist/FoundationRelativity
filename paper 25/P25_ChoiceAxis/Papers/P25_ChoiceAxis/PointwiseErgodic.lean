/-
Papers/P25_ChoiceAxis/PointwiseErgodic.lean
Paper 25: Dependent Choice ↔ Birkhoff's Pointwise Ergodic Theorem

**Part II of the paper**: The pointwise ergodic theorem calibrates to DC.

## Forward Direction: DC → Birkhoff

Axiomatized: Birkhoff's theorem is not in Mathlib, so the forward
direction (DC suffices for the proof) cannot be verified in Lean.

**Where DC enters the proof:**
The standard proof of Birkhoff's theorem proceeds via:
1. The maximal ergodic lemma (finite, no choice needed)
2. Showing the set where lim sup and lim inf differ by > ε has measure 0
3. Constructing the exceptional null set by intersecting over rational ε

Step (3) requires **dependent sequential refinement**: at each stage,
the approximation to the null set depends on the previous stage's bound.
This is precisely the structure of Dependent Choice.

**Metastability vs convergence**: The proof-mining literature (Kohlenbach,
Avigad-Gerhardy-Towsner 2010) shows that *metastable* versions of
Birkhoff's theorem are provable without DC. The gap between metastability
and full pointwise convergence is exactly where DC lives.

## Reverse Direction: Birkhoff → DC

In classical Lean, DC is provable from `Classical.choice` alone,
so `BirkhoffErgodicTheorem → DC` holds trivially. The constructive
content — that Birkhoff constructively implies DC — is at paper level.

**Constructive encoding strategy (for the paper, over BISH):**
Given a total relation R on X with initial x₀:
1. Build a shift system (Ω^ℕ, σ, μ) where Ω encodes the available
   choices at each step and μ is an appropriate product measure
2. A dependent choice sequence is a point ω ∈ Ω^ℕ satisfying coherence
3. Define an observable f whose Birkhoff averages converge iff a coherent
   choice path exists
4. Pointwise convergence for μ-a.e. ω yields a valid choice sequence

**References:**
- Birkhoff, *Proof of the ergodic theorem* (1931)
- Nuber, *A constructive ergodic theorem* (1972)
- Avigad, Gerhardy, Towsner, *Local stability of ergodic averages* (2010)
- Kohlenbach, *Applied Proof Theory* (2008)
-/
import Papers.P25_ChoiceAxis.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Dynamics.Ergodic.MeasurePreserving

namespace Papers.P25_ChoiceAxis

open MeasureTheory Filter

/-! ## Statement of Birkhoff's Pointwise Ergodic Theorem -/

/-- **Birkhoff's Pointwise Ergodic Theorem.**
    For a measure-preserving transformation T on a probability space
    and f ∈ L¹, the time averages (1/n) ∑_{k=0}^{n-1} f(T^k x)
    converge for μ-almost every x.

    Statement only — proof requires Mathlib infrastructure not yet available.
    The limit is the conditional expectation of f w.r.t. the invariant
    σ-algebra (which equals ∫ f dμ when the system is ergodic). -/
def BirkhoffErgodicTheorem : Prop :=
  ∀ (α : Type*) [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (T : α → α) (_hT : MeasurePreserving T μ μ)
    (f : α → ℝ) (_hf : Integrable f μ),
    ∃ g : α → ℝ, (∀ᵐ x ∂μ,
      Tendsto (fun n => (↑(n + 1))⁻¹ * ∑ k ∈ Finset.range (n + 1), f (T^[k] x))
        atTop (nhds (g x)))

/-! ## Forward Direction: DC → Birkhoff -/

/-- **DC implies Birkhoff's Pointwise Ergodic Theorem.**

    Axiomatized: Birkhoff's theorem is not yet in Mathlib, so we
    cannot verify the proof in Lean. The claim that DC suffices is
    based on analysis of the standard proof:
    - Maximal ergodic lemma: no choice needed (finite operations)
    - Null set construction: requires DC (dependent refinement)
    - Metastable version: provable without DC (Avigad-Gerhardy-Towsner)

    DC is used precisely to bridge the metastability-convergence gap.

    This is the only remaining axiom in the bundle. -/
axiom birkhoff_of_dc : DC → BirkhoffErgodicTheorem

/-! ## Reverse Direction: Birkhoff → DC -/

/-- **Birkhoff's Pointwise Ergodic Theorem implies DC.**

    In classical Lean, DC is provable from `Classical.choice` alone,
    so this implication holds trivially — the antecedent is unused.

    The mathematical content is a constructive claim (over BISH):
    if pointwise ergodic averages converge a.e. (Birkhoff), then
    dependent sequential constructions are possible (DC). The proof
    encodes DC problems into specific measure-preserving systems;
    see module docstring for the encoding strategy.

    This Lean proof witnesses classical validity; the constructive
    calibration is at paper level. -/
theorem dc_of_birkhoff : BirkhoffErgodicTheorem → DC := by
  intro _
  -- In classical Lean, DC is provable without any hypothesis.
  -- Classical.choice extracts witnesses from (∀ x, ∃ y, R x y).
  intro X R htotal x₀
  -- Build the step function: for each x, choose y with R x y
  have step : ∀ x : X, { y : X // R x y } :=
    fun x => ⟨(htotal x).choose, (htotal x).choose_spec⟩
  -- Build the sequence by recursion
  let f : ℕ → X := fun n => (fun g => (step g).val)^[n] x₀
  refine ⟨f, rfl, fun n => ?_⟩
  -- f (n+1) = step (f n), so R (f n) (f (n+1)) = (step (f n)).property
  show R (f n) (f (n + 1))
  simp only [f, Function.iterate_succ', Function.comp_def]
  exact (step _).property

/-- **Birkhoff's Theorem is equivalent to DC** (over BISH).
    Combines the forward and reverse directions.

    In classical Lean, the reverse direction is fully proved
    (DC is classically valid). The forward direction is axiomatized
    (Birkhoff's theorem is not in Mathlib).

    The equivalence depends on the single axiom `birkhoff_of_dc`. -/
theorem birkhoff_iff_dc : DC ↔ BirkhoffErgodicTheorem :=
  ⟨birkhoff_of_dc, dc_of_birkhoff⟩

end Papers.P25_ChoiceAxis
