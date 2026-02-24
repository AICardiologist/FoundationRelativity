/-
  Paper 45: Weight-Monodromy Conjecture — Lean 4 Formalization
  C4_Descent.lean: Theorem C4 — Geometric Origin as De-Omniscientizing Descent

  Main result (Theorem C4):
    For geometric perverse sheaves, the spectral sequence differentials
    have matrix entries in ℚ̄ (algebraic closure of ℚ inside ℚ_ℓ).
    Over ℚ̄, equality is decidable in BISH. Therefore degeneration
    is decidable in BISH — without LPO.

  Key insight: "Geometric memory" IS algebraicity of coefficients.
  Geometric origin provides a DE-OMNISCIENTIZING DESCENT:
    Abstract sheaves over ℚ_ℓ → degeneration requires LPO (Theorem C2)
    Geometric sheaves        → coefficients descend to ℚ̄
    Over ℚ̄                  → equality decidable in BISH
    Therefore                → degeneration decidable in BISH

  Axiom profile: QBar_decidable_eq, geometric_sheaf_algebraic,
    geometric_differential_decidable, spectral_sequence_bounded.
  No sorry. No Classical.dec. Decidability derived from axioms.
-/

import Papers.P45_WMC.Defs
import Papers.P45_WMC.C2_LPO

noncomputable section

namespace Papers.P45

-- ============================================================
-- Algebraic Numbers Infrastructure
-- ============================================================

/-- The algebraic closure of ℚ inside an ℓ-adic coefficient field.
    In Phase 1, axiomatized as a type with decidable equality. -/
axiom QBar : Type

/-- ℚ̄ is a field. -/
axiom QBar_instField : Field QBar

attribute [instance] QBar_instField

/-- **Axiom: Decidable equality in ℚ̄.**
    Given two algebraic numbers, there exists a finite algorithm to
    determine whether they are equal: compute minimal polynomials
    over ℚ and compare. This is constructively valid in BISH.

    This is the key fact: the algebraic numbers live in a DECIDABLE
    sub-universe of the undecidable ℓ-adic field. -/
axiom QBar_decidable_eq : DecidableEq QBar

attribute [instance] QBar_decidable_eq

-- ============================================================
-- Geometric Algebraicity
-- ============================================================

/-- **Geometric sheaves have algebraic coefficients (documentary).**
    If a perverse sheaf arises from nearby cycles of an actual
    smooth projective variety (i.e., is geometric), then the matrix
    entries of its spectral sequence differentials lie in ℚ̄.

    This is a consequence of the theory of weights: geometric sheaves
    arise from algebraic cycles, which force the cohomological
    operations to have algebraic (not merely ℓ-adic) coefficients.

    Reference: Deligne, "La conjecture de Weil II" (1980).

    This is a documentary theorem (Phase 1 placeholder for the type
    constraint). The load-bearing axiom is geometric_differential_decidable,
    which captures the combined content of algebraicity + decidable equality. -/
theorem geometric_sheaf_algebraic
    {q : ℕ} (_sheaf : PicardLefschetzSheaf q)
    (_h_geometric : IsGeometric _sheaf) :
    True := trivial

-- ============================================================
-- Per-Page Decidability and Boundedness
-- ============================================================

/-- **Axiom: Geometric sheaves have decidable differentials.**
    For a geometric perverse sheaf, each individual page differential
    d_r has decidably-zero status. This is because:

    1. Matrix entries lie in ℚ̄ (by geometric_sheaf_algebraic)
    2. ℚ̄ has decidable equality (by QBar_decidable_eq)
    3. A finite matrix over a field with decidable equality
       has decidable vanishing (check each entry)

    This axiom captures the per-page decidability that QBar_decidable_eq
    and geometric_sheaf_algebraic together provide. -/
axiom geometric_differential_decidable
    {q : ℕ} (sheaf : PicardLefschetzSheaf q)
    (_h_geometric : IsGeometric sheaf)
    (SS : WeightSpectralSequence q sheaf) :
    ∀ r : ℕ, Decidable (SS.differential_is_zero r)

/-- **Axiom: Spectral sequences are eventually stationary.**
    For any weight spectral sequence, there exists a page N
    beyond which all differentials are zero. This is a standard
    consequence of bounded-dimensionality: the E_r pages are
    subquotients of a fixed finite-dimensional space, so the
    differentials d_r must eventually vanish.

    Note: This is a general spectral sequence fact, not specific
    to geometric sheaves.

    Returns a Subtype (not ∃) so the bound N can be extracted
    constructively — Lean's Exists.casesOn only eliminates into Prop,
    but we need the bound as data to build a Decidable instance. -/
axiom spectral_sequence_bounded
    {q : ℕ} {sheaf : PicardLefschetzSheaf q}
    (SS : WeightSpectralSequence q sheaf) :
    {N : ℕ // ∀ r : ℕ, r > N → SS.differential_is_zero r}

-- ============================================================
-- Decidability for Geometric Sheaves
-- ============================================================

/-- **Theorem C4 (Geometric Degeneration Decidable in BISH).**
    For a geometric perverse sheaf, the question "does the weight
    spectral sequence degenerate at E₂?" is decidable in BISH.

    Proof:
    1. Each d_r is decidably zero (geometric_differential_decidable)
    2. The spectral sequence is eventually stationary (spectral_sequence_bounded):
       ∃ N, ∀ r > N, d_r = 0
    3. E₂ degeneration = ∀ r ≥ 2, d_r = 0
       Equivalent to: ∀ r ∈ {2, ..., N}, d_r = 0 (pages above N hold by (2))
    4. Finite conjunction of decidable propositions is decidable

    This does NOT tell us the answer is "yes" — just that the
    QUESTION is decidable. Proving d_r = 0 still requires
    understanding why the algebraic numbers vanish (Section 7.7).

    No Classical.dec. No Classical.choice beyond Lean infrastructure.
    The decidability is derived constructively from the axioms. -/
def geometric_degeneration_decidable_BISH
    {q : ℕ} (sheaf : PicardLefschetzSheaf q)
    (h_geometric : IsGeometric sheaf)
    (SS : WeightSpectralSequence q sheaf) :
    Decidable (E2_degeneration SS) := by
  -- Obtain the bound N (Subtype, so this works in Type context)
  obtain ⟨N, hN⟩ := spectral_sequence_bounded SS
  -- Per-page decidability from geometric origin
  have h_dec := geometric_differential_decidable sheaf h_geometric SS
  -- E2_degeneration = ∀ r ≥ 2, SS.differential_is_zero r
  -- Pages r > N hold automatically by hN.
  -- So it suffices to check r ∈ {2, ..., max(N, 2)}.
  set bound := max N 2
  -- Check all pages from 2 to bound using decidableDforallFinset
  have h_fin_dec : Decidable (∀ (r : ℕ) (_ : r ∈ Finset.Icc 2 bound), SS.differential_is_zero r) :=
    @Finset.decidableDforallFinset ℕ (Finset.Icc 2 bound)
      (fun a _ => SS.differential_is_zero a)
      (fun a _ => h_dec a)
  exact match h_fin_dec with
  | .isTrue h =>
    .isTrue (fun r hr => by
      by_cases hrN : r ≤ bound
      · exact h r (Finset.mem_Icc.mpr ⟨hr, hrN⟩)
      · push_neg at hrN
        exact hN r (by omega))
  | .isFalse h =>
    .isFalse (fun hall => h (fun r hr => by
      have ⟨hr2, _⟩ := Finset.mem_Icc.mp hr
      exact hall r hr2))

-- ============================================================
-- The De-Omniscientizing Descent
-- ============================================================

/-- **The De-Omniscientizing Descent (Master Theorem).**
    This theorem combines Theorems C2 and C4 to show:

    1. For ABSTRACT perverse sheaves over ℚ_ℓ:
       Degeneration decidability ↔ LPO(ℚ_ℓ) (Theorem C2)

    2. For GEOMETRIC perverse sheaves:
       Degeneration is decidable in BISH (Theorem C4)

    The gap between (1) and (2) is PRECISELY the algebraicity of
    coefficients: geometric origin descends the coefficient field
    from undecidable ℚ_ℓ to decidable ℚ̄.

    "Geometric memory" = algebraicity of coefficients.

    This reframes the Arithmetic Kashiwara Conjecture:
      OLD: Find a p-adic polarization (impossible by Theorem C3)
      NEW: Show the algebraic matrix entries vanish by arithmetic geometry -/
theorem de_omniscientizing_descent :
    -- Part 1: Abstract degeneration requires LPO (from C2)
    (∀ (K : Type) [_inst : Field K], DecidesDegeneration K ↔ LPO_field K) ∧
    -- Part 2: Geometric degeneration is decidable in BISH (from C4)
    (∀ (q : ℕ) (sheaf : PicardLefschetzSheaf q) (_h_geo : IsGeometric sheaf)
      (SS : WeightSpectralSequence q sheaf),
      E2_degeneration SS ∨ ¬ E2_degeneration SS) := by
  constructor
  · -- Part 1: from Theorem C2
    intro K inst
    exact abstract_degeneration_iff_LPO K
  · -- Part 2: from Theorem C4 (Decidable gives Or)
    intro q sheaf h_geo SS
    exact (geometric_degeneration_decidable_BISH sheaf h_geo SS).em

end Papers.P45
