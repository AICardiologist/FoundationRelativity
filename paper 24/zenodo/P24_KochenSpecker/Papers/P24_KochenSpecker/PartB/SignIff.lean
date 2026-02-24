/-
  Paper 24: LLPO Equivalence via Kochen-Specker Contextuality
  PartB/SignIff.lean — Sign of KS asymmetry decides LLPO

  Under AtMostOne:
    ksAsymmetry α ≤ 0  →  ∀ n, α(2n) = false
    0 ≤ ksAsymmetry α  →  ∀ n, α(2n+1) = false

  This is the core lemma connecting the sign decision to LLPO.
  Structurally identical to Paper 21's Bell asymmetry sign-iff lemmas.
-/
import Papers.P24_KochenSpecker.Defs.EncodedAsymmetry

namespace Papers.P24

noncomputable section

-- ========================================================================
-- Helper: AtMostOne + even true → all odd false
-- ========================================================================

/-- Under AtMostOne, if α(2k) = true then all odd entries are false. -/
theorem atMostOne_even_true_implies_odd_false (α : ℕ → Bool)
    (hamo : AtMostOne α) (k : ℕ) (hk : α (2 * k) = true) :
    ∀ j, α (2 * j + 1) = false := by
  intro j
  by_contra hj
  push_neg at hj
  have htj : α (2 * j + 1) = true := by
    cases h : α (2 * j + 1)
    · exact absurd h hj
    · rfl
  have := hamo (2 * k) (2 * j + 1) hk htj
  omega

/-- Under AtMostOne, if α(2k+1) = true then all even entries are false. -/
theorem atMostOne_odd_true_implies_even_false (α : ℕ → Bool)
    (hamo : AtMostOne α) (k : ℕ) (hk : α (2 * k + 1) = true) :
    ∀ j, α (2 * j) = false := by
  intro j
  by_contra hj
  push_neg at hj
  have htj : α (2 * j) = true := by
    cases h : α (2 * j)
    · exact absurd h hj
    · rfl
  have := hamo (2 * k + 1) (2 * j) hk htj
  omega

-- ========================================================================
-- Sign-iff: nonpositive → all even false
-- ========================================================================

/-- Under AtMostOne, if ksAsymmetry α ≤ 0, then all even entries are false.

    Proof: If some α(2k) = true, then evenField > 0 (by tsum_pos) and
    AtMostOne forces all odd entries false, so oddField = 0. Then
    ksAsymmetry = evenField - 0 > 0, contradicting ≤ 0. -/
theorem ksAsymmetry_nonpos_implies_even_false (α : ℕ → Bool)
    (hamo : AtMostOne α) (hle : ksAsymmetry α ≤ 0) :
    ∀ n, α (2 * n) = false := by
  intro n
  by_contra hne
  push_neg at hne
  have htrue : α (2 * n) = true := by
    cases h : α (2 * n)
    · exact absurd h hne
    · rfl
  -- evenField > 0
  have hterm_pos : 0 < evenFieldTerm α n := by
    unfold evenFieldTerm; rw [if_pos htrue]; apply pow_pos; norm_num
  have heven_pos : 0 < evenField α :=
    (evenField_summable α).tsum_pos (evenFieldTerm_nonneg α) n hterm_pos
  -- All odd entries false → oddField = 0
  have hodd_all : ∀ j, α (2 * j + 1) = false :=
    atMostOne_even_true_implies_odd_false α hamo n htrue
  have hodd_zero : oddField α = 0 := (oddField_eq_zero_iff α).mpr hodd_all
  -- ksAsymmetry = evenField - 0 > 0, contradicting ≤ 0
  unfold ksAsymmetry at hle
  linarith

-- ========================================================================
-- Sign-iff: nonnegative → all odd false
-- ========================================================================

/-- Under AtMostOne, if 0 ≤ ksAsymmetry α, then all odd entries are false.

    Symmetric to the above: if some α(2k+1) = true, then oddField > 0 and
    AtMostOne forces all even entries false, so evenField = 0. Then
    ksAsymmetry = 0 - oddField < 0, contradicting ≥ 0. -/
theorem ksAsymmetry_nonneg_implies_odd_false (α : ℕ → Bool)
    (hamo : AtMostOne α) (hge : 0 ≤ ksAsymmetry α) :
    ∀ n, α (2 * n + 1) = false := by
  intro n
  by_contra hne
  push_neg at hne
  have htrue : α (2 * n + 1) = true := by
    cases h : α (2 * n + 1)
    · exact absurd h hne
    · rfl
  -- oddField > 0
  have hterm_pos : 0 < oddFieldTerm α n := by
    unfold oddFieldTerm; rw [if_pos htrue]; apply pow_pos; norm_num
  have hodd_pos : 0 < oddField α :=
    (oddField_summable α).tsum_pos (oddFieldTerm_nonneg α) n hterm_pos
  -- All even entries false → evenField = 0
  have heven_all : ∀ j, α (2 * j) = false :=
    atMostOne_odd_true_implies_even_false α hamo n htrue
  have heven_zero : evenField α = 0 := (evenField_eq_zero_iff α).mpr heven_all
  -- ksAsymmetry = 0 - oddField < 0, contradicting ≥ 0
  unfold ksAsymmetry at hge
  linarith

end
end Papers.P24
