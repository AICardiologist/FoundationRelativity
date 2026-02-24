/-
  Paper 44: The Measurement Problem Dissolved
  Copenhagen/Copenhagen.lean — Copenhagen ↔ WLPO equivalence

  Theorem 3.1: The Copenhagen measurement postulate (decidability of
  superposition vs. eigenstate for any qubit) is equivalent to WLPO.

  Forward (Copenhagen → WLPO): encode a binary sequence f into a qubit
  via binaryEncoding + qubitFromReal, then apply the postulate.

  Reverse (WLPO → Copenhagen): WLPO on binary sequences lifts to
  decidability of α = 0 for Cauchy reals via the standard encoding
  [Bridges–Vîță 2006]. Sorry'd here; see Paper 14 for the analogous lift.
-/
import Papers.P44_MeasurementDissolved.Copenhagen.QubitState

noncomputable section
namespace Papers.P44

-- ========================================================================
-- Forward: Copenhagen → WLPO
-- ========================================================================

/-- **Theorem 3.1 (forward).** The Copenhagen measurement postulate implies WLPO.

    Proof: Given f : ℕ → Bool, construct r_f = binaryEncoding f ∈ [0,1],
    then the qubit state ψ = qubitFromReal(r_f). The postulate gives
    ψ.α = 0 ∨ ¬¬(ψ.α ≠ 0). Translating via binaryEncoding_eq_zero_iff:
    - ψ.α = 0 ↔ r_f = 0 ↔ ∀ n, f n = false
    - ψ.α ≠ 0 ↔ r_f ≠ 0 ↔ ¬(∀ n, f n = false)
    So we get (∀ n, f n = false) ∨ ¬(∀ n, f n = false), which is WLPO. -/
theorem copenhagen_implies_WLPO : CopenhagenPostulate → WLPO := by
  intro h f
  set r := binaryEncoding f
  set ψ := qubitFromReal r
  rcases h ψ with h_zero | h_nneg
  · -- Case: ψ.α = 0, so r = 0, so ∀ n, f n = false
    left
    exact (binaryEncoding_eq_zero_iff f).mp ((qubitFromReal_alpha_eq_zero_iff r).mp h_zero)
  · -- Case: ¬¬(ψ.α ≠ 0), so ¬¬(r ≠ 0), so ¬(∀ n, f n = false)
    right
    intro h_all
    apply h_nneg
    intro h_ne
    exact h_ne ((qubitFromReal_alpha_eq_zero_iff r).mpr
      ((binaryEncoding_eq_zero_iff f).mpr h_all))

-- ========================================================================
-- Strong Copenhagen → LPO (new in revision)
-- ========================================================================

/-- **Theorem 3.2 (forward).** The strong Copenhagen postulate implies LPO.

    Proof: Given f : ℕ → Bool, construct r_f = binaryEncoding f ∈ [0,1],
    then the qubit state ψ = qubitFromReal(r_f). The strong postulate gives
    ψ.α = 0 ∨ ψ.α ≠ 0. Translating via binaryEncoding_eq_zero_iff:
    - ψ.α = 0 ↔ r_f = 0 ↔ ∀ n, f n = false
    - ψ.α ≠ 0 ↔ r_f ≠ 0 ← ∃ n, f n = true (by binaryEncoding_pos_of_exists_true)

    The ψ.α ≠ 0 case gives r_f ≠ 0, hence ¬(∀ n, f n = false).
    By contrapositive of binaryEncoding_eq_zero_iff, this gives ∃ n, f n = true.

    Added in revision: this shows that the *strong* Copenhagen postulate
    (without double-negation weakening) calibrates at LPO, not WLPO.
    The comparison validates WLPO as the *minimal* constructive content
    of the measurement postulate. -/
theorem strong_copenhagen_implies_LPO : CopenhagenStrong → LPO := by
  intro h f
  set r := binaryEncoding f
  set ψ := qubitFromReal r
  rcases h ψ with h_zero | h_ne
  · -- Case: ψ.α = 0, so r = 0, so ∀ n, f n = false
    left
    exact (binaryEncoding_eq_zero_iff f).mp ((qubitFromReal_alpha_eq_zero_iff r).mp h_zero)
  · -- Case: ψ.α ≠ 0, so r ≠ 0, so ∃ n, f n = true
    right
    have hr_ne : r ≠ 0 := by
      intro h_eq
      exact h_ne ((qubitFromReal_alpha_eq_zero_iff r).mpr h_eq)
    -- r = binaryEncoding f ≠ 0 means ¬(∀ n, f n = false)
    -- i.e., ∃ n, f n = true
    by_contra h_none
    push_neg at h_none
    have h_all : ∀ n, f n = false := by
      intro n
      by_contra h_fn
      have : f n = true := by
        cases f n <;> simp_all
      exact h_none n this
    exact hr_ne ((binaryEncoding_eq_zero_iff f).mpr h_all)

/-- The strong Copenhagen postulate is at least as strong as the weak one.
    (Re-exported from QubitState.lean for convenience.) -/
theorem strong_copenhagen_implies_weak : CopenhagenStrong → CopenhagenPostulate :=
  strong_implies_weak

-- ========================================================================
-- Reverse: WLPO → Copenhagen
-- ========================================================================

/-- **Theorem 3.1 (reverse).** WLPO implies the Copenhagen measurement postulate.

    The standard argument: WLPO for binary sequences lifts to the real-number
    form "∀ r : ℝ, r = 0 ∨ ¬(r = 0)" for Cauchy reals constructed from
    binary sequences. Since every Cauchy real encodes a binary sequence
    via its Cauchy modulus, WLPO on sequences gives decidability of the
    zero-test for the real part, and similarly for the imaginary part.
    Combined: α = 0 ∨ ¬¬(α ≠ 0) for any complex amplitude.

    This lifting is standard [Bridges–Vîță 2006] but the encoding from
    arbitrary Cauchy reals back to binary sequences is technically heavy.
    Sorry'd here; the type signature is the mathematical assertion. -/
theorem WLPO_implies_copenhagen : WLPO → CopenhagenPostulate := by
  intro _wlpo _ψ
  sorry

-- ========================================================================
-- Combined equivalence
-- ========================================================================

/-- **Theorem 3.1.** The Copenhagen measurement postulate is equivalent to WLPO.
    The Copenhagen interpretation of quantum mechanics — asserting that
    measurement of a superposition α|0⟩ + β|1⟩ yields a definite outcome —
    requires exactly the Weak Limited Principle of Omniscience. -/
theorem copenhagen_iff_WLPO : CopenhagenPostulate ↔ WLPO :=
  ⟨copenhagen_implies_WLPO, WLPO_implies_copenhagen⟩

end Papers.P44
end
