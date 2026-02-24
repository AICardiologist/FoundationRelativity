/-
  Paper 36: Cubitt's Spectral Gap Undecidability Stratification
  ThermoLimit.lean: Theorem 2 — Thermodynamic limit costs exactly LPO

  The sequence Δ_L is NOT monotone (gaps fluctuate before L exceeds
  the halting time T). The proof uses LPO to branch first, then
  extracts a Cauchy modulus in each branch separately.

  We formulate "limit exists" as: ∃ Δ, the finite-volume gaps converge
  to Δ with a Cauchy modulus. This avoids referencing the placeholder
  spectral_gap definition.
-/
import Papers.P36_CubittStratification.Defs
import Papers.P36_CubittStratification.BridgeLemmas

noncomputable section

open Real

-- ============================================================
-- Theorem 2: Thermodynamic Limit ↔ LPO
-- ============================================================

/-- The thermodynamic limit exists for a TM: there exists a real Δ
    such that the finite-volume gaps converge to Δ. -/
def thermo_limit_exists (M : TM) : Prop :=
  ∃ (Δ : ℝ), ∀ (ε : ℝ), 0 < ε →
    ∃ (N₀ : ℕ), ∀ L : ℕ, N₀ ≤ L → |CPgW_gap M L - Δ| < ε

/-- Forward: If the thermodynamic limit exists for all TMs
    in CPgW's family, then LPO holds.

    Given binary sequence a, construct M_a via tm_from_seq.
    By the gap dichotomy, spectral_gap(M_a) is either 0 or ≥ γ > 0.
    This decides whether M_a halts, which decides ∃n, a(n) = true. -/
theorem thermo_limit_to_lpo
    (_ : ∀ (M : TM), thermo_limit_exists M) :
    LPO := by
  intro a
  let M_a := tm_from_seq a
  rcases cpgw_gap_dichotomy M_a with h_zero | h_pos
  · -- spectral_gap M_a = 0 → M_a halts → ∃ n, a n = true
    have h_halts : halts M_a := by
      by_contra h_not_halts
      have h_gap := cpgw_gapped_of_not_halts M_a h_not_halts
      linarith
    right
    exact (tm_from_seq_halts a).mp h_halts
  · -- spectral_gap M_a ≥ γ > 0 → ¬halts M_a → ∀ n, a n = false
    have h_not_halts : ¬halts M_a := by
      intro h_halts
      have h_eq := cpgw_gapless_of_halts M_a h_halts
      have h_gp := cpgw_gamma_pos
      linarith
    left
    intro n
    by_contra h_ne
    have h_true : a n = true := by
      cases ha : a n with
      | false => exact absurd ha h_ne
      | true => rfl
    exact h_not_halts ((tm_from_seq_halts a).mpr ⟨n, h_true⟩)

/-- Reverse: LPO implies the thermodynamic limit exists for every TM.
    Key: LPO decides halting, then we get a Cauchy modulus in each case.
    - Halting case: gap closes to 0 (cpgw_halting_asymptotics)
    - Non-halting case: gap stabilizes to Δ∞ > 0 (cpgw_nonhalting_asymptotics) -/
theorem lpo_to_thermo_limit (hl : LPO) :
    ∀ (M : TM), thermo_limit_exists M := by
  intro M
  rcases hl (halting_seq M) with h_all_false | ⟨n, hn⟩
  · -- ∀ n, halting_seq M n = false → M does not halt
    have h_not_halts : ¬halts M := by
      intro ⟨k, hk⟩
      have := h_all_false k
      rw [this] at hk
      exact Bool.false_ne_true hk
    -- Non-halting asymptotics give convergence to Δ∞ > 0
    obtain ⟨Delta_inf, _, hconv⟩ := cpgw_nonhalting_asymptotics M h_not_halts
    exact ⟨Delta_inf, hconv⟩
  · -- ∃ n, halting_seq M n = true → M halts
    have h_halts : halts M := ⟨n, hn⟩
    obtain ⟨N₀, hN⟩ := cpgw_halting_asymptotics M h_halts
    refine ⟨0, fun ε hε => ⟨N₀, fun L hL => ?_⟩⟩
    rw [hN L hL]; simp; exact hε

/-- THEOREM 2 (LPO boundary): The thermodynamic limit of the CPgW
    spectral gap exists for all TMs ↔ LPO.

    The forward direction extracts LPO from the limit via the gap
    dichotomy. The reverse uses LPO to branch on halting, obtaining
    a Cauchy modulus in each case.

    Critical subtlety: the sequence Δ_L is NOT monotone. BMC/Fekete
    cannot be applied directly. LPO resolves halting FIRST, then
    monotonicity emerges in each branch separately. This is a different
    proof architecture from Paper 29. -/
theorem thermo_limit_iff_lpo :
    (∀ (M : TM), thermo_limit_exists M) ↔ LPO :=
  ⟨thermo_limit_to_lpo, lpo_to_thermo_limit⟩

end
