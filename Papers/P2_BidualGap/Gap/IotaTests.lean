/-
Smoke tests for ι + lattice homomorphism identities.
-/
import Papers.P2_BidualGap.Gap.Iota
open Classical
open Papers.P2.Gap.BooleanSubLattice

section
  variable (A B : Set ℕ)

  -- injectivity modulo c₀
  example : (ι A ≈₀ ι B) ↔ indicatorEqModC0Spec A B :=
    iota_eq_iff_spec A B

  -- lattice laws hold pointwise, so also mod c₀:
  example : ι (A ∪ B) ≈₀ (fun n => max (ι A n) (ι B n)) :=
    iota_union_hom A B

  example : ι (A ∩ B) ≈₀ (fun n => min (ι A n) (ι B n)) :=
    iota_inter_hom A B

  example : ι (Aᶜ) ≈₀ (fun n => 1 - ι A n) :=
    iota_compl_hom A

  -- congruence under lattice ops with fixed third set
  variable (C : Set ℕ)

  example (h : ι A ≈₀ ι B) : ι (A ∪ C) ≈₀ ι (B ∪ C) :=
    iota_union_congr_right h

  example (h : ι A ≈₀ ι B) : ι (A ∩ C) ≈₀ ι (B ∩ C) :=
    iota_inter_congr_right h

  example (h : ι A ≈₀ ι B) : ι (Aᶜ) ≈₀ ι (Bᶜ) :=
    iota_compl_congr h

  -- left-hand congruence symmetry
  example (h : ι A ≈₀ ι B) : ι (C ∪ A) ≈₀ ι (C ∪ B) :=
    iota_union_congr_left h

  example (h : ι A ≈₀ ι B) : ι (C ∩ A) ≈₀ ι (C ∩ B) :=
    iota_inter_congr_left h

  -- concrete instance: ι ({0} ∪ C) ≈₀ ι (∅ ∪ C) whenever indicatorEqModC0Spec {0} ∅
  example : ι ({0} ∪ C) ≈₀ ι (∅ ∪ C) := by
    apply iota_union_congr_right
    -- {0} △ ∅ = {0} is finite, so use the spec → ι direction
    apply (iota_eq_iff_spec {0} ∅).2
    -- prove indicatorEqModC0Spec {0} ∅, i.e., symmDiff {0} ∅ is finite
    show indicatorEqModC0Spec {0} ∅
    unfold indicatorEqModC0Spec finiteSymmDiff 
      Papers.P2.Gap.BooleanSubLattice.symmDiff
    -- {0} △ ∅ = ({0} \ ∅) ∪ (∅ \ {0}) = {0} ∪ ∅ = {0}
    simpa using Set.finite_singleton 0
end