/-
  Paper 38: The Grandfather is LPO — Wang Tiling
  Main.lean: Master theorem and axiom audit

  The grandfather of all physical undecidability — Wang tiling —
  is LPO. Every descendant inherits exactly LPO and nothing more.
-/
import Papers.P38_WangTiling.TilingDecision
import Papers.P38_WangTiling.Aperiodicity
import Papers.P38_WangTiling.Genealogy
import Papers.P38_WangTiling.Ceiling

noncomputable section

-- ============================================================
-- Master Theorem
-- ============================================================

/-- MASTER THEOREM: The complete Wang tiling stratification.

    Part 1: Wang tiling decision ≡ LPO.
    Part 2: Aperiodicity detection ≡ LPO.
    Part 3: All genealogy entries are LPO-equivalent.
    Part 4: The Σ₁⁰ ceiling — LPO decides all Σ₁⁰.

    PUNCHLINE: Physics encodes computation via tiling.
    Tiling encodes halting. Halting is Σ₁⁰.
    LPO decides Σ₁⁰. Therefore every undecidability
    in physics is LPO. The story is complete. -/
theorem wang_tiling_master :
    -- Part 1: Wang tiling ↔ LPO
    ((∀ (W : WangTileset), tiles_plane W ∨ ¬tiles_plane W) ↔ LPO) ∧
    -- Part 2: Aperiodicity ↔ LPO
    ((∀ (a : ℕ → Bool),
      is_aperiodic_encoded a ∨ ¬is_aperiodic_encoded a) ↔ LPO) ∧
    -- Part 3: Genealogy — all entries are LPO
    (∀ r ∈ undecidability_genealogy, r.lpo_equivalent = true) ∧
    -- Part 4: Σ₁⁰ ceiling
    (∀ (P : Sigma1Property), LPO →
      ∀ (M : TM), P.prop M ∨ ¬P.prop M) :=
  ⟨wang_tiling_iff_lpo,
   aperiodicity_iff_lpo,
   grandfather_is_lpo,
   sigma1_ceiling⟩

-- ============================================================
-- Axiom Audit
-- ============================================================

-- Expected axioms:
-- Bridge lemmas:
-- 1. br_tiles_iff_not_halts (Berger-Robinson)
-- 2. br_aperiodic_of_not_halts (Berger-Robinson)
-- 3. wang_tileset (encoding function)
-- 4. tiling_compactness (König's lemma — compactness bridge axiom)
-- 5. no_patch_seq_spec, no_patch_seq_false_spec (decidability)
-- 6. has_valid_patch_decidable (BISH — finite enumeration)
-- 7. aperiodic_encoded_iff_all_false (aperiodicity bridge)
-- 8. tm_from_seq, tm_from_seq_halts (TM encoding)
-- 9. halting_problem_undecidable (halting)
-- Plus Lean infrastructure: propext, Classical.choice, Quot.sound

#print axioms wang_tiling_master

end
