/-
Papers/P26_GodelGap/CalibrationLink.lean
Paper 26: The Gödel-Gap Correspondence

Connection to the WLPO calibration from Paper 2.

The Paper 2 result: deciding whether an element of ℓ∞/c₀ is zero
is equivalent to WLPO. The Gödel-Gap correspondence specializes this:
deciding whether a Gödel-Gap element is zero is equivalent to deciding
consistency of the corresponding Π⁰₁ sentence, which is equivalent to WLPO.

This completes the interpretive circle:
  WLPO ↔ bidual gap detection (Paper 2)
  bidual gap detection ↔ arithmetic consistency decision (Paper 26)
  ∴ WLPO ↔ arithmetic consistency decision

## Custom Axiom

One axiom: `pi01_decidable_implies_wlpo`, encoding the well-known
equivalence between WLPO and the decidability of Π⁰₁ consistency.
This follows from the standard characterization of WLPO as
"∀α: ℕ → 2, (∀n. αn = 0) ∨ ¬(∀n. αn = 0)" applied to the
characteristic function of bounded proof search.
-/
import Papers.P26_GodelGap.Correspondence

namespace Papers.P26_GodelGap

open Classical

-- ========================================================================
-- WLPO and Π⁰₁ consistency
-- ========================================================================

/-- Decidability of Π⁰₁ consistency: for every Π⁰₁ sentence φ,
    either φ is consistent or φ is refutable. -/
def Pi01ConsistencyDecidable : Prop :=
  ∀ φ : Pi01, ConsistentPA φ.val ∨ RefutablePA φ.val

/-- WLPO implies Π⁰₁ consistency is decidable.

    Given WLPO and a Π⁰₁ sentence φ, define the binary sequence
    α(n) = true if there exists p ≤ n with PrfPA p (¬φ), else false.
    Then:
    - (∀n. α(n) = false) ↔ ConsistentPA φ
    - ¬(∀n. α(n) = false) ↔ RefutablePA φ
    WLPO decides which holds. -/
theorem wlpo_implies_pi01_decidable : WLPO → Pi01ConsistencyDecidable := by
  intro hwlpo φ
  -- Define the binary sequence tracking bounded proof search:
  -- α(n) = true  if ∃ p ≤ n, PrfPA p (¬φ)
  -- α(n) = false otherwise
  let α : ℕ → Bool := fun n =>
    if ∃ p, p ≤ n ∧ PrfPA p (negPA φ.val) then true else false
  have hα := hwlpo α
  cases hα with
  | inl hall =>
    -- All entries are false: no refutation exists at any bound → consistent
    left
    intro ⟨p, hp⟩
    -- α(p) should be true (since p ≤ p and PrfPA p (negPA φ.val))
    have : α p = true := if_pos ⟨p, le_refl p, hp⟩
    -- But hall says α(p) = false
    rw [hall p] at this
    exact Bool.noConfusion this
  | inr hsome =>
    -- Some entry is not false: a refutation exists → refutable
    right
    by_contra hcon
    apply hsome
    intro n
    show (if ∃ p, p ≤ n ∧ PrfPA p (negPA φ.val) then true else false) = false
    rw [if_neg]
    push_neg
    intro p hp hprf
    exact hcon ⟨p, hprf⟩

/-- Π⁰₁ consistency decidability implies WLPO.

    Given a binary sequence α : ℕ → Bool, construct the Π⁰₁ sentence
    "∀n. α(n) = 0" (which is Π⁰₁ because α is computable).
    Deciding consistency of this sentence decides whether α is all-zero.

    We axiomatize this direction because constructing the actual Gödel
    sentence requires Gödel numbering (out of scope). -/
axiom pi01_decidable_implies_wlpo : Pi01ConsistencyDecidable → WLPO

/-- **WLPO ↔ Π⁰₁ Consistency Decidability**: the logical content of
    gap detection in ℓ∞/c₀ is exactly the decidability of arithmetic
    consistency of Π⁰₁ sentences. -/
theorem wlpo_iff_pi01_decidable : WLPO ↔ Pi01ConsistencyDecidable :=
  ⟨wlpo_implies_pi01_decidable, pi01_decidable_implies_wlpo⟩

-- ========================================================================
-- Connection to gap detection
-- ========================================================================

/-- Gap detection: decidability of whether a Gödel-Gap element is zero. -/
def GapDetectionDecidable : Prop :=
  ∀ φ : Pi01, godelGapMap (LindenbaumPi01.mk φ) = BidualGap.zero ∨
              godelGapMap (LindenbaumPi01.mk φ) ≠ BidualGap.zero

/-- Π⁰₁ consistency decidability ↔ gap detection decidability.
    This follows directly from the gap detection theorem. -/
theorem pi01_decidable_iff_gap_detection :
    Pi01ConsistencyDecidable ↔ GapDetectionDecidable := by
  constructor
  · intro h φ
    cases h φ with
    | inl hcon => right; exact godelGapMap_consistent_ne_zero φ hcon
    | inr href => left; exact godelGapMap_refutable φ href
  · intro h φ
    cases h φ with
    | inl hzero =>
      right
      exact (godelGap_detects_refutability φ).mp hzero
    | inr hnonzero =>
      left
      intro href
      exact hnonzero (godelGapMap_refutable φ href)

-- ========================================================================
-- The calibration chain
-- ========================================================================

/-- **Calibration Chain**: WLPO ↔ Π⁰₁ consistency ↔ gap detection. -/
theorem calibration_chain :
    (WLPO ↔ Pi01ConsistencyDecidable) ∧
    (Pi01ConsistencyDecidable ↔ GapDetectionDecidable) :=
  ⟨wlpo_iff_pi01_decidable, pi01_decidable_iff_gap_detection⟩

/-- **Main Calibration Theorem**: WLPO ↔ Gap Detection.
    The direct composition of the chain. -/
theorem wlpo_iff_gap_detection : WLPO ↔ GapDetectionDecidable :=
  wlpo_iff_pi01_decidable.trans pi01_decidable_iff_gap_detection

end Papers.P26_GodelGap
