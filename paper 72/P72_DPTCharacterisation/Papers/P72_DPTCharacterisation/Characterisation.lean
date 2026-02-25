/-
  Paper 72: The DPT Characterisation — Full Assembly

  Combines:
    Theorem A (Minimality): each axiom necessary.
    Theorem B (Height-Search): positive-definite ↔ BISH for cycle-search.
    Theorem C (Characterisation): DPT axioms are minimal for BISH motivic arithmetic.

  The Archimedean Principle (Paper 70) is thereby sharpened:
    Paper 70: "the logical cost of mathematics is the logical cost of ℝ" (forward).
    Paper 72: "and this cost is necessary, not merely sufficient" (reverse).

  What this does NOT claim (correcting v1):
    - NOT that Rep_ℚ(G) is undecidable for non-compact G.
    - NOT that Fargues-Scholze must secretly invoke ℝ.
      (FS works at a different level: categorical, not cycle-search.)
    - YES that cycle-search for algebraic cycles requires positive-definiteness
      from the Archimedean place.
-/
import Papers.P72_DPTCharacterisation.HeightSearch
import Papers.P72_DPTCharacterisation.Minimality

open CRMLevel HeightType

-- ============================================================
-- The DPT Characterisation Theorem
-- ============================================================

/-- **THEOREM C (DPT Characterisation):**
    For the motivic cycle-search problem:

    Axiom 3 (Archimedean polarisation) ↔ BISH cycle-search decidability.

    Forward: Axiom 3 → positive-definite height → Northcott → BISH.
    Reverse: BISH cycle-search → positive-definite height → Axiom 3
             (contrapositive: indefinite → LPO → not BISH).

    Combined with Axioms 1 and 2 (separately necessary):
    DPT Axioms 1 ∧ 2 ∧ 3 are the minimal axioms for BISH-decidable
    motivic arithmetic.

    Scope limitation: this characterises the cycle-search problem,
    not all possible motivic constructions. Whether alternative
    axiomatisations achieve BISH for DIFFERENT questions remains open. -/
theorem dpt_characterisation :
    -- Each axiom is necessary
    (without_A1_cost = LPO)
    ∧ (without_A2_cost = WLPO)
    -- Axiom 3 ↔ BISH cycle-search (the new result)
    ∧ (cycle_search_cost positive_definite = BISH)
    ∧ (cycle_search_cost indefinite = LPO)
    -- Archimedean place is the only source of positive-definiteness
    ∧ (cycle_search_cost (available_height real_completion) = BISH)
    ∧ (cycle_search_cost (available_height padic_completion) = LPO) := by
  exact ⟨without_A1_cost_eq,
         without_A2_cost_eq,
         positive_definite_gives_BISH,
         indefinite_gives_LPO,
         (archimedean_necessary_for_search).1,
         (archimedean_necessary_for_search).2⟩

-- ============================================================
-- The Sharpened Archimedean Principle
-- ============================================================

/-- **COROLLARY (Archimedean Principle, sharpened):**
    Paper 70: ℝ is sufficient for BISH cycle-search (forward).
    Paper 72: ℝ is necessary for BISH cycle-search (reverse).
    Together: the Archimedean place is the unique source of
    positive-definiteness (via u(ℝ) = ∞), and positive-definiteness
    is the unique mechanism for BISH cycle-search (via Northcott). -/
theorem archimedean_principle_sharpened (c : CompletionProfile) :
    cycle_search_cost (available_height c) = BISH ↔
    c.is_archimedean = true := by
  cases c with
  | mk arch u_fin =>
    cases arch
    · -- arch = false (p-adic): available_height = indefinite
      show cycle_search_cost indefinite = BISH ↔ false = true
      constructor
      · intro h; rw [indefinite_gives_LPO] at h; exact absurd h (by decide)
      · intro h; exact absurd h (by decide)
    · -- arch = true (real): available_height = positive_definite
      show cycle_search_cost positive_definite = BISH ↔ true = true
      exact ⟨fun _ => rfl, fun _ => positive_definite_gives_BISH⟩

-- ============================================================
-- Verification
-- ============================================================

#check dpt_minimality
#check height_search_equivalence
#check archimedean_necessary_for_search
#check dpt_characterisation
#check archimedean_principle_sharpened
