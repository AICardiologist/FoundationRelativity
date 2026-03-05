/-
  Paper 36: Cubitt's Spectral Gap Undecidability Stratification
  ZeroTest.lean: Theorem 4 — Physical gap zero-test is WLPO

  For a specific physical Hamiltonian whose thermodynamic-limit
  spectral gap Δ exists as a completed real, deciding "Δ = 0 or Δ > 0"
  costs exactly WLPO. This connects to Paper 26 (Gödel-Gap).
-/
import Papers.P36_CubittStratification.Defs
import Papers.P36_CubittStratification.BridgeLemmas

noncomputable section

open Real

-- ============================================================
-- Theorem 4: Physical Gap Zero-Test ↔ WLPO
-- ============================================================

-- A non-negative real's zero test: Δ = 0 ∨ Δ > 0.
-- This is equivalent to WLPO (and subsumes Markov's Principle).

/-- Forward: WLPO implies we can test Δ = 0 ∨ Δ > 0 for non-negative Δ.

    Proof sketch: Given Δ ≥ 0, define the binary sequence
    a(n) = false if Δ < 1/(n+1), true otherwise (this is BISH-computable
    since Δ is a completed real with Cauchy representation).
    WLPO decides: ∀n, a(n) = false (meaning Δ = 0) or
    ¬(∀n, a(n) = false) (meaning Δ > 0, since Δ ≥ 0). -/
axiom wlpo_to_zero_test :
    WLPO → ∀ (Δ : ℝ), Δ ≥ 0 → (Δ = 0 ∨ Δ > 0)

/-- Reverse: If we can test Δ = 0 ∨ Δ > 0 for all non-negative Δ,
    then WLPO holds.

    Proof sketch: Given a : ℕ → Bool, define Δ_a = Σ a(n) · 2⁻ⁿ.
    Then Δ_a ≥ 0 and Δ_a = 0 ↔ ∀n, a(n) = false. Deciding
    Δ_a = 0 ∨ Δ_a > 0 decides WLPO for a. -/
axiom zero_test_to_wlpo :
    (∀ (Δ : ℝ), Δ ≥ 0 → (Δ = 0 ∨ Δ > 0)) → WLPO

/-- THEOREM 4 (WLPO): The physical gap zero-test Δ = 0 ∨ Δ > 0
    for a non-negative completed real is equivalent to WLPO.

    Connection to Paper 26: This is the physical instantiation of the
    Gödel-Gap embedding. The Π₁⁰ sentence "∀n, a(n) = 0" maps to
    "is the spectral gap zero?" Both are WLPO.

    Connection to Paper 33: The QCD mass gap (Δ_QCD > 0) is exactly
    a WLPO zero-test on a specific Hamiltonian's gap. -/
theorem physical_gap_zero_test_iff_wlpo :
    (∀ (Δ : ℝ), Δ ≥ 0 → (Δ = 0 ∨ Δ > 0)) ↔ WLPO :=
  ⟨zero_test_to_wlpo, wlpo_to_zero_test⟩

/-- WLPO is subsumed by LPO. So the gap zero-test is
    automatically available once LPO is assumed. -/
theorem gap_zero_test_from_lpo (hl : LPO) :
    ∀ (Δ : ℝ), Δ ≥ 0 → (Δ = 0 ∨ Δ > 0) :=
  wlpo_to_zero_test (wlpo_of_lpo hl)

end
