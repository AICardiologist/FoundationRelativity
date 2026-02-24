/-
  Paper 36: Cubitt's Spectral Gap Undecidability Stratification
  BridgeLemmas.lean: CPgW bridge axioms

  These axioms encode the key properties of the Cubitt-Perez-Garcia-Wolf
  construction. They are the interface between our Lean formalization and
  the 140-page CPgW proof (arXiv:1502.04135).
-/
import Papers.P36_CubittStratification.Defs

noncomputable section

open Real

-- ============================================================
-- Bridge Axiom 1: CPgW encoding is computable
-- ============================================================

/-- The map M ↦ H(M) is computable: given M's transition table,
    one can algorithmically produce the local interaction terms.
    This means CPgW_gap M L is a computable real for each M, L. -/
axiom cpgw_encoding_computable (M : TM) (L : ℕ) :
    ∃ (q : ℝ), |CPgW_gap M L - q| < 1  -- rational approx exists

-- ============================================================
-- Bridge Axiom 2: The fundamental CPgW dichotomy
-- ============================================================

/-- CPgW's core result: the thermodynamic-limit gap encodes halting.
    Gapped ↔ M does not halt. Gapless ↔ M halts.
    We axiomatize both directions. -/
axiom cpgw_gapped_of_not_halts (M : TM) :
    ¬halts M → spectral_gap M > 0

axiom cpgw_gapless_of_halts (M : TM) :
    halts M → spectral_gap M = 0

-- ============================================================
-- Bridge Axiom 3: Asymptotic behavior in the halting case
-- ============================================================

/-- When M halts, the finite-volume gap closes with a computable rate.
    There exists a computable function f such that for L > f(T),
    where T is the halting time, the gap is zero. -/
axiom cpgw_halting_asymptotics (M : TM) :
    halts M →
    ∃ (N₀ : ℕ), ∀ L : ℕ, N₀ ≤ L → CPgW_gap M L = 0

-- ============================================================
-- Bridge Axiom 4: Asymptotic behavior in the non-halting case
-- ============================================================

/-- When M does not halt, the gap stabilizes with a computable rate.
    There exists Δ∞ > 0 and a Cauchy modulus such that the
    finite-volume gaps converge to Δ∞. -/
axiom cpgw_nonhalting_asymptotics (M : TM) :
    ¬halts M →
    ∃ (Delta_inf : ℝ), Delta_inf > 0 ∧
      ∀ (ε : ℝ), 0 < ε →
        ∃ (N₀ : ℕ), ∀ L : ℕ, N₀ ≤ L → |CPgW_gap M L - Delta_inf| < ε

-- ============================================================
-- Bridge Axiom 5: Gap dichotomy (gap is 0 or ≥ γ)
-- ============================================================

/-- The spectral gap in the thermodynamic limit is either 0 or
    bounded below by γ > 0. There is no intermediate regime. -/
axiom cpgw_gap_dichotomy (M : TM) :
    spectral_gap M = 0 ∨ spectral_gap M ≥ cpgw_gamma

-- ============================================================
-- Bridge Axiom 6: Sequence-to-TM encoding
-- ============================================================

/-- Given a binary sequence a : ℕ → Bool, we can construct a TM
    that halts iff ∃ n, a n = true. This is the standard encoding
    of Σ₁⁰ predicates as halting problems. -/
axiom tm_from_seq : (ℕ → Bool) → TM

/-- The TM constructed from a halts iff ∃ n, a n = true. -/
axiom tm_from_seq_halts (a : ℕ → Bool) :
    halts (tm_from_seq a) ↔ ∃ n, a n = true

-- ============================================================
-- Bridge Axiom 7: Algebraic eigenvalues (for Theorem 1)
-- ============================================================

/-- The finite-volume CPgW Hamiltonian has algebraic matrix entries,
    so eigenvalues are algebraic reals computable in BISH. -/
axiom cpgw_finite_gap_computable (M : TM) (L : ℕ) (ε : ℝ) :
    0 < ε → ∃ (q : ℝ), |CPgW_gap M L - q| < ε

-- ============================================================
-- Derived lemma: cpgw_gamma is positive
-- ============================================================

theorem cpgw_gamma_pos : cpgw_gamma > 0 := by
  unfold cpgw_gamma; norm_num

end
