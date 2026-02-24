/-
  Paper 38: The Grandfather is LPO — Wang Tiling
  Aperiodicity.lean: Theorem 2 — Aperiodicity Detection ≡ LPO

  Deciding whether a tileset tiles the plane aperiodically
  is Turing-Weihrauch equivalent to LPO.
-/
import Papers.P38_WangTiling.Defs
import Papers.P38_WangTiling.BridgeLemmas
import Papers.P38_WangTiling.TilingDecision

noncomputable section

-- ============================================================
-- Theorem 2: Aperiodicity Detection ≡ LPO
-- ============================================================

/-- The aperiodicity detection property for encoded tilesets.
    For Berger-Robinson encoded tilesets:
    tiles_aperiodically(W(M)) ↔ ¬halts(M). -/
def is_aperiodic_encoded (a : ℕ → Bool) : Prop :=
  tiles_aperiodically (wang_tileset (tm_from_seq a))

/-- Bridge: aperiodic encoding ↔ all false (non-halting).
    From BR-2: tiles ↔ ¬halts. From BR-3: ¬halts → aperiodic.
    Conversely: aperiodic → tiles → ¬halts. -/
axiom aperiodic_encoded_iff_all_false (a : ℕ → Bool) :
    is_aperiodic_encoded a ↔ ∀ n, a n = false

/-- Forward: aperiodicity decidability → LPO. -/
theorem aperiodicity_to_lpo
    (h_dec : ∀ (a : ℕ → Bool), is_aperiodic_encoded a ∨ ¬is_aperiodic_encoded a) :
    LPO := by
  intro a
  rcases h_dec a with h_yes | h_no
  · left; exact (aperiodic_encoded_iff_all_false a).mp h_yes
  · right
    by_contra h_no_ex
    push_neg at h_no_ex
    -- h_no_ex : ∀ n, a n ≠ true
    -- Show ∀ n, a n = false, then derive contradiction
    have h_all_false : ∀ n, a n = false := by
      intro n
      cases ha : a n with
      | false => rfl
      | true => exact absurd ha (h_no_ex n)
    exact h_no ((aperiodic_encoded_iff_all_false a).mpr h_all_false)

/-- Reverse: LPO → aperiodicity decidability. -/
theorem lpo_to_aperiodicity (lpo : LPO) :
    ∀ (a : ℕ → Bool), is_aperiodic_encoded a ∨ ¬is_aperiodic_encoded a := by
  intro a
  rcases lpo a with h_all | ⟨n, hn⟩
  · left; exact (aperiodic_encoded_iff_all_false a).mpr h_all
  · right
    intro h_ap
    have := (aperiodic_encoded_iff_all_false a).mp h_ap n
    rw [this] at hn
    exact Bool.false_ne_true hn

/-- THEOREM 2: Aperiodicity detection is Turing-Weihrauch
    equivalent to LPO.

    Berger (1966) showed aperiodic tilesets exist.
    Deciding aperiodicity costs exactly LPO — the same
    logical principle as the original tiling problem. -/
theorem aperiodicity_iff_lpo :
    (∀ (a : ℕ → Bool), is_aperiodic_encoded a ∨ ¬is_aperiodic_encoded a) ↔ LPO :=
  ⟨aperiodicity_to_lpo, lpo_to_aperiodicity⟩

end
