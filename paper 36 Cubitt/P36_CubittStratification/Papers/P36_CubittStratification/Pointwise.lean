/-
  Paper 36: Cubitt's Spectral Gap Undecidability Stratification
  Pointwise.lean: Theorem 3 — Pointwise decidability is LPO

  For any specific TM M, the question "Is H(M) gapped or gapless?"
  is decidable given LPO. This is a single application of LPO to
  the halting sequence, followed by a CPgW bridge lemma.
-/
import Papers.P36_CubittStratification.Defs
import Papers.P36_CubittStratification.BridgeLemmas

noncomputable section

open Real

-- ============================================================
-- Theorem 3: Pointwise LPO-Decidability
-- ============================================================

/-- THEOREM 3 (LPO): For any specific TM M, LPO decides whether
    H(M) is gapped or gapless.

    Proof: Apply LPO to halting_seq M. Either ∀n, h_n = false
    (M doesn't halt → gapped by CPgW), or ∃n, h_n = true
    (M halts → gapless by CPgW). -/
theorem pointwise_gap_decidable (M : TM) (hl : LPO) :
    spectral_gap M > 0 ∨ spectral_gap M = 0 := by
  rcases hl (halting_seq M) with h_all_false | ⟨n, hn⟩
  · -- ∀ n, halting_seq M n = false → M does not halt
    have h_not_halts : ¬halts M := by
      intro ⟨k, hk⟩
      have := h_all_false k
      rw [this] at hk
      exact Bool.false_ne_true hk
    left
    exact cpgw_gapped_of_not_halts M h_not_halts
  · -- ∃ n, halting_seq M n = true → M halts
    right
    exact cpgw_gapless_of_halts M ⟨n, hn⟩

/-- The gap status is determined for each specific TM. -/
def pointwise_gap_status (M : TM) (_ : LPO) : GapStatus :=
  if spectral_gap M > 0 then .Gapped else .Gapless

/-- Equivalently: LPO decides "is H(M) gapped?" for each M. -/
theorem lpo_decides_each_instance (hl : LPO) :
    ∀ (M : TM), spectral_gap M > 0 ∨ spectral_gap M = 0 :=
  fun M => pointwise_gap_decidable M hl

end
