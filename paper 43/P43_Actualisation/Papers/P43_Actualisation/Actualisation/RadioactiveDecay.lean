/-
  Paper 43: What the Ceiling Means
  Actualisation/RadioactiveDecay.lean — The three-step actualisation chain

  The chain: BISH → Cournot → ¬∀ → MP → ∃
    Step 1 (BISH): P(survive forever) = 0  [measure of eternal survival is zero]
    Step 2 (Cournot): actual atom ∉ eternal survival set  [¬(∀t, undecayed)]
    Step 3 (MP): from ¬(∀t, undecayed) extract ∃t, decayed  [Markov's Principle]

  Step 1 is mathematics. Step 2 is a physical postulate. Step 3 is MP.
-/
import Papers.P43_Actualisation.Defs.Cournot
import Papers.P43_Actualisation.Defs.Decay
import Papers.P43_Actualisation.Hierarchy.LPOImpliesMP

namespace Papers.P43

open MeasureTheory

-- ========================================================================
-- Step 1 (BISH): Eternal survival has measure zero
-- ========================================================================

/-- BRIDGE AXIOM: The measure of the eternal survival set is zero.
    This encodes the probability model: the countable intersection
    ⋂ₜ {ω | undecayed ω t} has measure zero because
    lim_{t→∞} exp(-λt) = 0.

    The mathematical content (lim exp(-λt) = 0) is BISH and proved
    in ExponentialWitness.lean. This axiom bridges that to the
    measure-space formulation. -/
axiom survival_prob_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (undecayed : Ω → ℕ → Prop) (rate : ℝ) (_hr : 0 < rate)
    (_h_model : ∀ t, μ {ω | undecayed ω t} =
      ENNReal.ofReal (survivalProb rate ↑t)) :
    μ (eternalSurvival undecayed) = 0

-- ========================================================================
-- Step 2 (Cournot): The actual atom does not survive forever
-- ========================================================================

/-- Cournot + BISH: the actual atom does not survive forever.
    Applies Cournot's Principle to the measure-zero eternal survival set. -/
theorem not_eternal_survival
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (undecayed : Ω → ℕ → Prop) (rate : ℝ) (hr : 0 < rate)
    (h_model : ∀ t, μ {ω | undecayed ω t} =
      ENNReal.ofReal (survivalProb rate ↑t))
    (ω : Ω) :
    ¬(∀ t, undecayed ω t) := by
  intro h_all
  exact cournot (survival_prob_zero undecayed rate hr h_model) ω h_all

-- ========================================================================
-- Step 3 (MP): Extract the decay witness
-- ========================================================================

/-- Actualisation theorem for radioactive decay.
    BISH + Cournot + MP → ∃t, the atom has decayed by time t.

    The boolean predicate `decayed` makes the sequence decidable,
    which is required for MP (binary sequence form). -/
theorem atom_decays_mp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (hMP : MarkovPrinciple)
    (decayed : Ω → ℕ → Bool)
    (undecayed : Ω → ℕ → Prop)
    (h_equiv : ∀ ω t, undecayed ω t ↔ decayed ω t = false)
    (rate : ℝ) (hr : 0 < rate)
    (h_model : ∀ t, μ {ω | undecayed ω t} =
      ENNReal.ofReal (survivalProb rate ↑t))
    (ω : Ω) :
    ∃ t, decayed ω t = true := by
  apply hMP (fun n => decayed ω n)
  intro h_all_false
  apply not_eternal_survival undecayed rate hr h_model ω
  intro t
  rw [h_equiv]
  exact h_all_false t

end Papers.P43
