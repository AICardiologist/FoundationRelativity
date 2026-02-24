/-
  Paper 38: The Grandfather is LPO — Wang Tiling
  BridgeLemmas.lean: Berger-Robinson encoding axioms

  The Berger-Robinson encoding maps TMs to Wang tilesets
  such that W(M) tiles the plane iff M does not halt.
-/
import Papers.P38_WangTiling.Defs

noncomputable section

-- ============================================================
-- Berger-Robinson Encoding (Bridge Lemmas)
-- ============================================================

/-- The Berger-Robinson encoding: maps a TM to a Wang tileset.
    The tiles encode the transition function of M. -/
axiom wang_tileset : TM → WangTileset

/-- BR-1: The encoding M ↦ W(M) is computable.
    (Each tile encodes one transition rule — finite construction.) -/
axiom br_encoding_computable :
    ∀ (M : TM), wang_tileset M = wang_tileset M  -- placeholder for computability

/-- BR-2: W(M) tiles ℤ² iff M does NOT halt.
    If M halts at step T, the computation history terminates
    and cannot fill the infinite plane. If M doesn't halt,
    the computation history extends indefinitely. -/
axiom br_tiles_iff_not_halts (M : TM) :
    tiles_plane (wang_tileset M) ↔ ¬halts M

/-- BR-3: If M doesn't halt, W(M) tiles aperiodically.
    The computation never terminates, so the history explores
    new tape cells indefinitely, preventing periodicity. -/
axiom br_aperiodic_of_not_halts (M : TM) :
    ¬halts M → tiles_aperiodically (wang_tileset M)

-- ============================================================
-- Tiling Compactness (König's lemma — compactness bridge axiom)
-- ============================================================

/-- Whether a given n-by-n region admits a valid patch.
    This is BISH-decidable: enumerate all |W|^(n²) assignments
    and check edge-matching. -/
axiom has_valid_patch : WangTileset → ℕ → Prop

/-- Checking n×n patches is decidable (finite enumeration). -/
axiom has_valid_patch_decidable (W : WangTileset) (n : ℕ) :
    Decidable (has_valid_patch W n)

/-- Tiling compactness: W tiles ℤ² iff for all n,
    there exists a valid n×n patch.
    This is König's lemma for finitely branching trees — a
    compactness bridge axiom, NOT BISH-provable.
    The tree of partial tilings has branching factor |W|^(n²),
    finite for each n, but extracting the infinite path
    requires WKL or equivalent. -/
axiom tiling_compactness (W : WangTileset) :
    tiles_plane W ↔ ∀ (n : ℕ), has_valid_patch W n

/-- "Doesn't tile" is witnessed by a blocking size. -/
theorem not_tiles_iff_blocking (W : WangTileset) :
    ¬tiles_plane W ↔ ∃ (n : ℕ), ¬has_valid_patch W n := by
  rw [tiling_compactness]
  push_neg
  rfl

/-- The patch-checking sequence as a Bool function
    (for applying LPO). -/
def no_patch_seq (W : WangTileset) : ℕ → Bool :=
  fun n => if (has_valid_patch_decidable W n).decide then false else true

/-- no_patch_seq n = true iff there's no valid n×n patch. -/
axiom no_patch_seq_spec (W : WangTileset) (n : ℕ) :
    no_patch_seq W n = true ↔ ¬has_valid_patch W n

/-- no_patch_seq n = false iff there IS a valid n×n patch. -/
axiom no_patch_seq_false_spec (W : WangTileset) (n : ℕ) :
    no_patch_seq W n = false ↔ has_valid_patch W n

end
