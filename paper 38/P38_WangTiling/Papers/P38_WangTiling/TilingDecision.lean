/-
  Paper 38: The Grandfather is LPO — Wang Tiling
  TilingDecision.lean: Theorem 1 — Wang Tiling Decision ≡ LPO

  The grandfather of all physical undecidability:
  Berger's theorem (1966) that the Wang tiling problem is undecidable.
  CRM stratification: exactly LPO.
-/
import Papers.P38_WangTiling.Defs
import Papers.P38_WangTiling.BridgeLemmas

noncomputable section

-- ============================================================
-- Theorem 1: Wang Tiling Decision ≡ LPO
-- ============================================================

/-- Forward: If we can decide tiling for all tilesets, then LPO holds.

    Given binary sequence a, construct M_a, then W(M_a).
    W(M_a) tiles ↔ M_a doesn't halt ↔ ∀n, a(n) = false.
    Deciding tiling decides LPO. -/
theorem tiling_to_lpo
    (h_dec : ∀ (W : WangTileset), tiles_plane W ∨ ¬tiles_plane W) :
    LPO := by
  intro a
  let M_a := tm_from_seq a
  let W_a := wang_tileset M_a
  rcases h_dec W_a with h_tiles | h_not_tiles
  · -- W_a tiles → M_a doesn't halt → ∀n, a(n) = false
    left
    have h_not_halts : ¬halts M_a := (br_tiles_iff_not_halts M_a).mp h_tiles
    intro n
    by_contra h_ne
    have h_true : a n = true := by
      cases ha : a n with
      | false => exact absurd ha h_ne
      | true => rfl
    exact h_not_halts ((tm_from_seq_halts a).mpr ⟨n, h_true⟩)
  · -- W_a doesn't tile → M_a halts → ∃n, a(n) = true
    right
    have h_halts : halts M_a := by
      by_contra h_not_halts
      exact h_not_tiles ((br_tiles_iff_not_halts M_a).mpr h_not_halts)
    exact (tm_from_seq_halts a).mp h_halts

/-- Reverse: LPO implies we can decide tiling for any tileset.

    Given W, compute no_patch_seq W (BISH for each n).
    Apply LPO: either ∃n with no valid n×n patch (doesn't tile),
    or ∀n has valid patch (tiles by compactness). -/
theorem lpo_to_tiling (lpo : LPO) :
    ∀ (W : WangTileset), tiles_plane W ∨ ¬tiles_plane W := by
  intro W
  rcases lpo (no_patch_seq W) with h_all_false | ⟨n, hn⟩
  · -- ∀n, no_patch_seq W n = false → ∀n, has_valid_patch W n → tiles
    left
    rw [tiling_compactness]
    intro n
    exact (no_patch_seq_false_spec W n).mp (h_all_false n)
  · -- ∃n, no_patch_seq W n = true → ∃n, ¬has_valid_patch W n → doesn't tile
    right
    rw [not_tiles_iff_blocking]
    exact ⟨n, (no_patch_seq_spec W n).mp hn⟩

/-- THEOREM 1: The Wang tiling problem is Turing-Weihrauch
    equivalent to LPO.

    Wang (1961) conjectured decidability. Berger (1966) refuted it.
    CRM reveals: the undecidability is exactly LPO — the same
    principle as thermodynamic limits. -/
theorem wang_tiling_iff_lpo :
    (∀ (W : WangTileset), tiles_plane W ∨ ¬tiles_plane W) ↔ LPO :=
  ⟨tiling_to_lpo, lpo_to_tiling⟩

end
