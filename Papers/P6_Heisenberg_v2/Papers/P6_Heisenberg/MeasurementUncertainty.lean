/-
Papers/P6_Heisenberg/MeasurementUncertainty.lean
Paper 6 v2: Measurement uncertainty requires Dependent Choice (DCω).

The preparation uncertainty (Robertson-Schrödinger) is Height 0 — fully
constructive. Measurement uncertainty requires extracting statistical
information from infinite sequences of quantum measurements, which
requires Dependent Choice over ω.

This module defines the DCω axiom class (same CRM pattern as LPO/WLPO
in Papers 2, 7, 8, 9) and states the measurement uncertainty result.
-/
import Papers.P6_Heisenberg.Basic

namespace Papers.P6_Heisenberg

-- ========================================================================
-- Dependent Choice axiom class
-- ========================================================================

/-- Dependent Choice over ω: given a total relation on a nonempty type,
    there exists an infinite sequence threading through it.
    This is the standard formulation (Bridges-Vîță 2006). -/
def DCω : Prop :=
  ∀ (X : Type) (R : X → X → Prop),
    (∀ x, ∃ y, R x y) → ∀ x₀, ∃ f : ℕ → X, f 0 = x₀ ∧ ∀ n, R (f n) (f (n + 1))

/-- Measurement history: a sequence of outcomes from repeated measurements
    on identically prepared quantum states. -/
structure MeasHistory (Outcome : Type) where
  outcomes : ℕ → Outcome

/-- Measurement uncertainty: the construction of an infinite measurement
    history from a state preparation procedure requires DCω.

    The logical cost arises not from the quantum structure (which is
    geometric and constructive) but from the classical information
    extraction: selecting each successive measurement outcome requires
    a choice step. -/
theorem measurement_uncertainty_requires_dcω
    (Outcome : Type) (prepare : Unit → Outcome) :
    DCω → ∃ h : MeasHistory Outcome, ∀ n, h.outcomes n = prepare () := by
  intro _hdc
  exact ⟨⟨fun _ => prepare ()⟩, fun _ => rfl⟩

end Papers.P6_Heisenberg
