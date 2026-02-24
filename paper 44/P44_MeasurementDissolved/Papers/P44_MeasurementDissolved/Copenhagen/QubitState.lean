/-
  Paper 44: The Measurement Problem Dissolved
  Copenhagen/QubitState.lean — Qubit state and encoding from reals

  A qubit state |ψ⟩ = α|0⟩ + β|1⟩ is a pair (α, β) of complex amplitudes
  with |α|² + |β|² = 1. The Copenhagen postulate asserts that measurement
  yields a definite outcome, requiring decidability of α = 0.
-/
import Papers.P44_MeasurementDissolved.Defs.BinaryEncoding
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
namespace Papers.P44

-- ========================================================================
-- Qubit state
-- ========================================================================

/-- A qubit state: a pair (α, β) of complex amplitudes with |α|² + |β|² = 1. -/
structure QubitState where
  α : ℂ
  β : ℂ
  norm_eq : Complex.normSq α + Complex.normSq β = 1

-- ========================================================================
-- Copenhagen postulate
-- ========================================================================

/-- The Copenhagen measurement postulate for a qubit:
    given |ψ⟩ = α|0⟩ + β|1⟩, measurement yields a definite outcome.
    This requires deciding whether the |0⟩ component is present,
    i.e., whether α = 0 (outcome 1 is certain) or α ≠ 0 (outcome 0 is possible).

    Constructively, the weakest version asserts: α = 0 ∨ ¬¬(α ≠ 0).
    The double negation reflects that "α ≠ 0" is undecidable in BISH,
    but we can at least assert that α = 0 is not refutable. -/
def CopenhagenPostulate : Prop :=
  ∀ (ψ : QubitState), ψ.α = 0 ∨ ¬¬(ψ.α ≠ 0)

-- ========================================================================
-- Strong Copenhagen postulate (LPO-strength)
-- ========================================================================

/-- The strong Copenhagen measurement postulate for a qubit:
    given |ψ⟩ = α|0⟩ + β|1⟩, measurement yields a definite outcome
    with full decidability: α = 0 ∨ α ≠ 0.

    This is the version where measurement outcome is *positively decided*,
    not merely ¬¬-stable. It corresponds to α = 0 ∨ α ≠ 0 for complex
    amplitudes, which is LPO-strength for reals (not WLPO).

    Added in revision to address referee concerns about the double-negation
    weakening in `CopenhagenPostulate`. The comparison between the two
    formalizations quantifies the constructive cost of strengthening the
    postulate from WLPO to LPO. -/
def CopenhagenStrong : Prop :=
  ∀ (ψ : QubitState), ψ.α = 0 ∨ ψ.α ≠ 0

/-- The strong postulate implies the weak postulate.
    If α = 0 ∨ α ≠ 0, then α = 0 ∨ ¬¬(α ≠ 0), since P → ¬¬P. -/
theorem strong_implies_weak : CopenhagenStrong → CopenhagenPostulate := by
  intro h ψ
  rcases h ψ with h_zero | h_ne
  · exact Or.inl h_zero
  · exact Or.inr (not_not_intro h_ne)

-- ========================================================================
-- Constructing qubit states from reals
-- ========================================================================

/-- Helper: r² + 1 > 0 for any real r. -/
theorem sq_add_one_pos (r : ℝ) : 0 < r ^ 2 + 1 := by positivity

/-- Helper: √(r² + 1) > 0 for any real r. -/
theorem sqrt_sq_add_one_pos (r : ℝ) : 0 < Real.sqrt (r ^ 2 + 1) :=
  Real.sqrt_pos_of_pos (sq_add_one_pos r)

/-- Helper: √(r² + 1) ≠ 0 for any real r. -/
theorem sqrt_sq_add_one_ne_zero (r : ℝ) : Real.sqrt (r ^ 2 + 1) ≠ 0 :=
  ne_of_gt (sqrt_sq_add_one_pos r)

/-- Construct a qubit state from a real number r:
    α = r / √(r²+1), β = 1 / √(r²+1).
    This always satisfies |α|² + |β|² = 1 and α = 0 ↔ r = 0. -/
def qubitFromReal (r : ℝ) : QubitState where
  α := ↑(r / Real.sqrt (r ^ 2 + 1))
  β := ↑(1 / Real.sqrt (r ^ 2 + 1))
  norm_eq := by
    have hsqrt_pos : 0 < Real.sqrt (r ^ 2 + 1) := sqrt_sq_add_one_pos r
    have hsqrt_ne : Real.sqrt (r ^ 2 + 1) ≠ 0 := ne_of_gt hsqrt_pos
    have hsq : Real.sqrt (r ^ 2 + 1) * Real.sqrt (r ^ 2 + 1) = r ^ 2 + 1 := by
      rw [← sq]; exact Real.sq_sqrt (le_of_lt (sq_add_one_pos r))
    simp only [Complex.normSq_ofReal]
    have hne : r ^ 2 + 1 ≠ 0 := ne_of_gt (sq_add_one_pos r)
    field_simp
    linarith [sq_nonneg r]

/-- The α component of qubitFromReal is zero iff r is zero. -/
theorem qubitFromReal_alpha_eq_zero_iff (r : ℝ) :
    (qubitFromReal r).α = 0 ↔ r = 0 := by
  simp only [qubitFromReal, Complex.ofReal_eq_zero]
  constructor
  · intro h
    have h' := div_eq_zero_iff.mp h
    rcases h' with h' | h'
    · exact h'
    · exact absurd h' (sqrt_sq_add_one_ne_zero r)
  · intro h
    simp [h]

/-- The α component of qubitFromReal is nonzero iff r is nonzero. -/
theorem qubitFromReal_alpha_ne_zero_iff (r : ℝ) :
    (qubitFromReal r).α ≠ 0 ↔ r ≠ 0 := by
  rw [not_iff_not]
  exact qubitFromReal_alpha_eq_zero_iff r

end Papers.P44
end
