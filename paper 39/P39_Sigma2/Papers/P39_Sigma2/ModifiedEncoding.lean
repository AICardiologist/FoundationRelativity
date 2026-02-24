/-
  Paper 39: Physics Reaches Σ₂⁰ — The Thermodynamic Stratification
  ModifiedEncoding.lean: Theorem 1 — The modified Cubitt encoding

  M ↦ H*(M): translation-invariant Hamiltonian on ℤ² where
  - H*(M) is gapped  ↔ {k : M halts on k within 16^k} is finite
  - H*(M) is gapless ↔ {k : M halts on k within 16^k} is infinite

  This encodes the Finiteness Problem into the spectral gap.
-/
import Papers.P39_Sigma2.Defs

noncomputable section

-- ============================================================
-- Bridge Lemmas: Modified Cubitt Construction
-- ============================================================

-- The modified encoding is computable (M ↦ H*(M))
-- Uses Robinson tiling + perimeter counter + input-dependent TM
-- (Bausch-Cubitt-Ozols 2018 technique)
axiom modified_encoding_computable :
    ∀ (_M : TM), True  -- placeholder for computability of the encoding

-- ============================================================
-- The Key Encoding: gapped ↔ finite halting set
-- ============================================================

-- BRIDGE LEMMA: Gapped ↔ finite halting set
-- The spectral gap is positive iff M halts on only finitely many inputs
-- (within the 16^k step bound at each scale)
axiom modified_gapped_iff_finite (M : TM) :
    is_gapped (modified_hamiltonian M) ↔ finiteness_problem M

-- BRIDGE LEMMA: Gapless ↔ infinite halting set
-- The spectral gap is zero iff M halts on infinitely many inputs
axiom modified_gapless_iff_infinite (M : TM) :
    is_gapless (modified_hamiltonian M) ↔ ¬finiteness_problem M

-- ============================================================
-- Theorem 1: The Modified Encoding Theorem
-- ============================================================

-- Part (a): gapped ↔ finite
theorem modified_encoding_gapped (M : TM) :
    is_gapped (modified_hamiltonian M) ↔ Set.Finite (halting_set M) :=
  modified_gapped_iff_finite M

-- Part (b): gapless ↔ infinite
theorem modified_encoding_gapless (M : TM) :
    is_gapless (modified_hamiltonian M) ↔ ¬Set.Finite (halting_set M) :=
  modified_gapless_iff_infinite M

-- ============================================================
-- Why There Is No Promise Gap
-- ============================================================

-- In the original Cubitt construction, the gap is either 0 or ≥ γ.
-- In the modified construction, the gap can be any value in [0, γ].
-- If M halts on finitely many inputs up to k_max, the gap is
-- min(γ, ε_1, ..., ε_{k_max}), which depends on halting times
-- and can be arbitrarily close to 0.

-- The gapped/gapless decision is equivalent to the Finiteness Problem.
-- The Finiteness Problem is Σ₂⁰-complete (not Σ₁⁰).
-- Therefore the spectral gap decision for the modified encoding
-- requires LPO_jump, not merely LPO.

-- Consistency check: gapped and gapless are complementary
theorem modified_gapped_gapless_complement (M : TM) :
    is_gapped (modified_hamiltonian M) ↔
    ¬is_gapless (modified_hamiltonian M) :=
  gapped_iff_not_gapless _

end
