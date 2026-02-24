/-
  Paper 43: What the Ceiling Means
  Defs/Cournot.lean — Cournot's Principle (bridge axiom)

  Cournot's Principle (1843): An event whose probability is zero
  does not occur in a single realisation of the experiment.

  This is a physical postulate, not a mathematical theorem.
  It bridges mathematical probability and empirical physics.
  Without it, probability theory describes ensembles only.
  With it, measure-zero exclusions become physical impossibilities.
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace

namespace Papers.P43

/-- Cournot's Principle (1843). BRIDGE AXIOM.
    An event of probability zero does not occur in a single
    realisation of the experiment.
    This is a physical postulate encoding the bridge between
    mathematical probability and empirical observation. -/
axiom cournot {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {A : Set Ω} (hA : μ A = 0) (ω : Ω) (hω : ω ∈ A) : False

/-- Cournot contrapositive: if ω exists and ω ∈ A, then μ(A) ≠ 0. -/
theorem cournot_contrapositive {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {A : Set Ω} (ω : Ω) (hω : ω ∈ A) :
    μ A ≠ 0 :=
  fun h => cournot h ω hω

end Papers.P43
