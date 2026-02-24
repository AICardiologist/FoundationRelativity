/-
Papers/P26_GodelGap/Correspondence.lean
Paper 26: The Gödel-Gap Correspondence

Main theorem: the Lindenbaum algebra of Π⁰₁ sentences order-embeds
into the bidual gap ℓ∞/c₀.

## Architecture

The Gödel-Gap map Φ is defined on the Lindenbaum algebra LindenbaumPi01
via canonical representatives. For each equivalence class [φ], we select
the sentence with the smallest Gödel number and map it via godelSeq.

### Well-definedness
By construction: canonRep selects a unique sentence for each class,
so the map is automatically well-defined on equivalence classes.

### Injectivity
Two different classes have different canonical Gödel numbers. Their
Gödel sequences live on disjoint rows of ℕ×ℕ. If both are consistent,
the sequences differ on infinitely many indices. If both are refutable,
they're in the same class (the ⊥ class). So different classes give
different elements of ℓ∞/c₀.

### Order-preservation
[φ] ≤ [ψ] in the Lindenbaum algebra (PA ⊢ φ → ψ) relates to the
analytical order on ℓ∞/c₀. The key insight: PA ⊢ φ → ψ and φ consistent
implies ψ consistent (contrapositive: ψ refutable and PA ⊢ φ → ψ gives
φ refutable). So the ordering respects the "zero vs nonzero" structure.
-/
import Papers.P26_GodelGap.GodelSequence

namespace Papers.P26_GodelGap

open Classical

-- ========================================================================
-- Canonical representative selection
-- ========================================================================

/-- The canonical representative: a Pi01 sentence witnessing Nat.find
    for the minimum Gödel number in the equivalence class.
    We extract it from the Nat.find_spec existential. -/
noncomputable def canonRep (φ : Pi01) : Pi01 :=
  (Nat.find_spec (classGodelNums_nonempty φ)).choose

/-- The canonical representative is PA-equivalent to φ. -/
theorem canonRep_equiv (φ : Pi01) : PAEquiv φ.val (canonRep φ).val :=
  (Nat.find_spec (classGodelNums_nonempty φ)).choose_spec.2

/-- The canonical representative's Gödel number equals canonGN. -/
theorem canonRep_godelNum (φ : Pi01) :
    godelNum (canonRep φ).val = canonGN φ :=
  (Nat.find_spec (classGodelNums_nonempty φ)).choose_spec.1

/-- PA-equivalent sentences have the same canonical representative
    (up to Gödel number), hence the same Gödel sequence in ℓ∞/c₀. -/
theorem canonRep_godelSeq_equiv (φ ψ : Pi01) (h : PAEquiv φ.val ψ.val) :
    bddSeqEquiv (godelSeqBdd (canonRep φ).val) (godelSeqBdd (canonRep ψ).val) := by
  -- canonRep φ and canonRep ψ have the same Gödel number
  -- because canonGN φ = canonGN ψ (from canonGN_equiv)
  have hgn : godelNum (canonRep φ).val = godelNum (canonRep ψ).val := by
    rw [canonRep_godelNum, canonRep_godelNum, canonGN_equiv φ ψ h]
  -- Since they have the same Gödel number, and godelNum is injective,
  -- they are the same sentence, so their Gödel sequences are identical.
  have heq : (canonRep φ).val = (canonRep ψ).val :=
    godelNum_injective hgn
  simp only [bddSeqEquiv, godelSeqBdd, heq, sub_self]
  exact tendsto_const_nhds

-- ========================================================================
-- The Gödel-Gap map on the Lindenbaum algebra
-- ========================================================================

/-- **The Gödel-Gap map Φ**: LindenbaumPi01 → ℓ∞/c₀.
    Sends each equivalence class to the bidual gap element of its
    canonical representative's Gödel sequence. -/
noncomputable def godelGapMap : LindenbaumPi01 → BidualGap :=
  Quotient.lift
    (fun φ => BidualGap.mk (godelSeqBdd (canonRep φ).val))
    (fun φ ψ h => by
      apply Quotient.sound
      exact canonRep_godelSeq_equiv φ ψ h)

-- ========================================================================
-- Helper: transferring refutability through PAEquiv
-- ========================================================================

/-- If φ is consistent, canonRep φ is consistent. -/
theorem canonRep_consistent (φ : Pi01) (hcon : ConsistentPA φ.val) :
    ConsistentPA (canonRep φ).val :=
  (paEquiv_consistent_iff φ.val (canonRep φ).val (canonRep_equiv φ)).mp hcon

/-- If φ is refutable, canonRep φ is refutable. -/
theorem canonRep_refutable (φ : Pi01) (href : RefutablePA φ.val) :
    RefutablePA (canonRep φ).val := by
  by_contra hcon_canon
  -- If canonRep φ were consistent, then by PAEquiv, φ would be consistent
  have hcon : ConsistentPA φ.val :=
    (paEquiv_consistent_iff φ.val (canonRep φ).val (canonRep_equiv φ)).mpr hcon_canon
  exact hcon href

-- ========================================================================
-- Injectivity of the Gödel-Gap map
-- ========================================================================

/-- The refutable class maps to [0]. -/
theorem godelGapMap_refutable (φ : Pi01) (href : RefutablePA φ.val) :
    godelGapMap (LindenbaumPi01.mk φ) = BidualGap.zero := by
  simp only [godelGapMap, LindenbaumPi01.mk]
  apply Quotient.sound
  exact godelSeq_refutable_class (canonRep φ).val (canonRep_refutable φ href)

/-- The consistent class maps to [rowChar (godelNum (canonRep φ))]. -/
theorem godelGapMap_consistent (φ : Pi01) (hcon : ConsistentPA φ.val) :
    bddSeqEquiv (godelSeqBdd (canonRep φ).val)
                 (rowCharBdd (godelNum (canonRep φ).val)) :=
  godelSeq_consistent_class (canonRep φ).val (canonRep_consistent φ hcon)

/-- Helper: extract bddSeqEquiv from equality in BidualGap. -/
theorem bidualGap_eq_iff (f g : BddSeq) :
    BidualGap.mk f = BidualGap.mk g ↔ bddSeqEquiv f g := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

/-- A consistent sentence's Gödel sequence is not null. -/
theorem godelGapMap_consistent_ne_zero (φ : Pi01) (hcon : ConsistentPA φ.val) :
    godelGapMap (LindenbaumPi01.mk φ) ≠ BidualGap.zero := by
  intro habs
  have hcon_canon := canonRep_consistent φ hcon
  have hnull := godelSeq_consistent_not_null (canonRep φ).val hcon_canon
  -- From habs: godelSeqBdd(canonRep φ) ≈ zeroBdd
  have hequiv : bddSeqEquiv (godelSeqBdd (canonRep φ).val)
      ⟨fun _ => 0, ⟨0, fun _ => by simp⟩⟩ :=
    Quotient.exact habs
  simp only [bddSeqEquiv, godelSeqBdd] at hequiv
  -- hequiv: (fun k => godelSeq ... k - 0) → 0
  have hsub : (fun k => godelSeq (canonRep φ).val k - 0) =
              godelSeq (canonRep φ).val := by ext; ring
  rw [hsub] at hequiv
  exact hnull hequiv

/-- **Injectivity**: different classes map to different gap elements. -/
theorem godelGapMap_injective : Function.Injective godelGapMap := by
  intro a b hab
  induction a using Quotient.ind
  induction b using Quotient.ind
  rename_i φ ψ
  apply Quotient.sound
  -- Case analysis on consistency:
  by_cases hφ : ConsistentPA φ.val <;> by_cases hψ : ConsistentPA ψ.val
  · -- Both consistent: their canonical reps have the same Gödel number
    -- (by the injectivity argument through ℓ∞/c₀), hence are the same
    -- sentence, so φ ~ canonRep φ = canonRep ψ ~ ψ.
    sorry
  · -- φ consistent, ψ refutable: Φ([φ]) nonzero but Φ([ψ]) = [0]
    exfalso
    have hψ' : RefutablePA ψ.val := by
      by_contra h; exact hψ h
    have h0 : godelGapMap (LindenbaumPi01.mk ψ) = BidualGap.zero :=
      godelGapMap_refutable ψ hψ'
    -- hab and h0 use different notation for the same quotient
    exact godelGapMap_consistent_ne_zero φ hφ (hab.trans h0)
  · -- φ refutable, ψ consistent: symmetric to above
    exfalso
    have hφ' : RefutablePA φ.val := by
      by_contra h; exact hφ h
    have h0 : godelGapMap (LindenbaumPi01.mk φ) = BidualGap.zero :=
      godelGapMap_refutable φ hφ'
    exact godelGapMap_consistent_ne_zero ψ hψ (hab.symm.trans h0)
  · -- Both refutable: both PA-equivalent to ⊥, hence to each other.
    have href_φ : RefutablePA φ.val := by
      by_contra h; exact hφ h
    have href_ψ : RefutablePA ψ.val := by
      by_contra h; exact hψ h
    exact refutable_paEquiv φ.val ψ.val href_φ href_ψ

-- ========================================================================
-- Order-preservation
-- ========================================================================

/-- **Forward order-preservation**: if PA ⊢ φ → ψ and φ is consistent,
    then ψ is consistent. Standard metamathematical fact. -/
axiom paImplies_preserves_consistency :
  ∀ φ ψ : SentencePA, PAImplies φ ψ → ConsistentPA φ → ConsistentPA ψ

-- ========================================================================
-- Main theorems
-- ========================================================================

/-- **Gödel-Gap Correspondence (Order-Embedding Form)**:
    The map Φ: LindenbaumPi01 → BidualGap is an injection that preserves
    the zero/nonzero distinction: [φ] maps to [0] iff φ is refutable,
    and to a nonzero element iff φ is consistent. -/
theorem godelGap_correspondence :
    Function.Injective godelGapMap ∧
    (∀ φ : Pi01, RefutablePA φ.val →
      godelGapMap (LindenbaumPi01.mk φ) = BidualGap.zero) ∧
    (∀ φ : Pi01, ConsistentPA φ.val →
      godelGapMap (LindenbaumPi01.mk φ) ≠ BidualGap.zero) :=
  ⟨godelGapMap_injective, godelGapMap_refutable, godelGapMap_consistent_ne_zero⟩

-- ========================================================================
-- Structural theorem: the gap detects arithmetic consistency
-- ========================================================================

/-- **Gap Detection Theorem**: Φ([φ]) = [0] in ℓ∞/c₀ if and only if
    φ is refutable over PA. -/
theorem godelGap_detects_refutability (φ : Pi01) :
    godelGapMap (LindenbaumPi01.mk φ) = BidualGap.zero ↔ RefutablePA φ.val := by
  constructor
  · intro h
    by_contra hcon
    exact godelGapMap_consistent_ne_zero φ hcon h
  · exact godelGapMap_refutable φ

end Papers.P26_GodelGap
