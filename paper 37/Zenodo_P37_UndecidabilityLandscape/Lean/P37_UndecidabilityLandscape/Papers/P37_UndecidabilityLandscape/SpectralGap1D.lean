/-
  Paper 37: Uncomputability of Phase Diagrams and RG Flows is LPO
  SpectralGap1D.lean: Theorem 2 — 1D Spectral Gap Undecidability ≡ LPO

  Bausch, Cubitt, Lucia, Perez-Garcia (2020, Phys. Rev. X):
  The spectral gap is undecidable even for 1D spin chains.
  CRM stratification: same as 2D — exactly LPO.
-/
import Papers.P37_UndecidabilityLandscape.Defs
import Papers.P37_UndecidabilityLandscape.MetaTheorem

noncomputable section

open Real

-- ============================================================
-- BCLPG Bridge Lemmas
-- ============================================================

-- BCLPG construct a 1D Hamiltonian whose spectral gap encodes halting.
-- The reduction M ↦ H₁D(M) has the same logical structure as CPgW.

/-- BCLPG 1D gap status: maps a TM to gapped/gapless. -/
axiom bclpg_gap_status : TM → GapStatus

/-- BCLPG bridge: gapless ↔ halts. -/
axiom bclpg_gapless_iff_halts (M : TM) :
    bclpg_gap_status M = GapStatus.Gapless ↔ halts M

/-- BCLPG bridge: gapped ↔ doesn't halt. -/
axiom bclpg_gapped_iff_not_halts (M : TM) :
    bclpg_gap_status M = GapStatus.Gapped ↔ ¬halts M

/-- The local dimension is fixed (doesn't grow with the TM). -/
axiom bclpg_local_dim : ℕ

-- ============================================================
-- Theorem 2: 1D Spectral Gap ≡ LPO
-- ============================================================

/-- The 1D gap decision: a sequence encodes a TM that is gapless. -/
def is_1d_gapless (a : ℕ → Bool) : Prop :=
  bclpg_gap_status (tm_from_seq a) = GapStatus.Gapless

/-- Encoding bridge: 1D gapless ↔ ∃n, a(n) = true. -/
theorem is_1d_gapless_iff_exists (a : ℕ → Bool) :
    is_1d_gapless a ↔ ∃ n, a n = true := by
  unfold is_1d_gapless
  rw [bclpg_gapless_iff_halts, tm_from_seq_halts]

/-- THEOREM 2: 1D spectral gap undecidability (BCLPG 2020) is
    Turing-Weihrauch equivalent to LPO.

    The dimensionality of the lattice does not affect the logical
    structure. 1D and 2D spectral gap undecidability have the
    same constructive cost. -/
theorem spectral_gap_1d_iff_lpo :
    (∀ (a : ℕ → Bool), is_1d_gapless a ∨ ¬is_1d_gapless a) ↔ LPO :=
  halting_reduction_iff_lpo
    (fun a => a)
    is_1d_gapless
    is_1d_gapless_iff_exists

/-- The uniform 1D gap function is not computable. -/
theorem gap_1d_not_computable :
    ¬(∀ (a : ℕ → Bool), is_1d_gapless a ∨ ¬is_1d_gapless a) :=
  uniform_function_not_computable
    (fun a => a)
    is_1d_gapless
    is_1d_gapless_iff_exists

/-- Given LPO, every 1D instance is decidable. -/
theorem gap_1d_decidable_from_lpo (lpo : LPO) :
    ∀ (a : ℕ → Bool), is_1d_gapless a ∨ ¬is_1d_gapless a :=
  spectral_gap_1d_iff_lpo.mpr lpo

end
