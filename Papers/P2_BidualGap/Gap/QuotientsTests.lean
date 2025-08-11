/-
Pin-safe smoke tests for the spec-level quotients + ῑ.
-/
import Papers.P2_BidualGap.Gap.Quotients
import Papers.P2_BidualGap.Gap.IndicatorSpec
import Papers.P2_BidualGap.Gap.Iota

open Classical
open Papers.P2.Gap.BooleanSubLattice

-- helper notation for clarity:
local notation "⟦" A "⟧ᵇ" => Quot.mk instSetoidSetNat.r A

section
  variable (A B : Set ℕ)

  -- Basic: finite △ ⇒ equal in the Boolean quotient
  example (hAB : (Papers.P2.Gap.BooleanSubLattice.symmDiff A B).Finite) :
      ⟦A⟧ᵇ = ⟦B⟧ᵇ :=
    Quot.sound (by simpa [Papers.P2.Gap.BooleanSubLattice.FinSymmDiffRel] using hAB)

  -- Descended embedding agrees on equivalent classes
  example (hAB : (Papers.P2.Gap.BooleanSubLattice.symmDiff A B).Finite) :
      iotaBar ⟦A⟧ᵇ = iotaBar ⟦B⟧ᵇ :=
    iotaBar_eq_of_finite_symmDiff hAB

  -- Concrete sanity check: {0} ∼ ∅ ⇒ ῑ[{0}] = ῑ[∅]
  example :
      iotaBar ⟦({0} : Set ℕ)⟧ᵇ = iotaBar ⟦(∅ : Set ℕ)⟧ᵇ := by
    refine iotaBar_eq_of_finite_symmDiff ?h
    -- ({0} △ ∅) = {0} is finite
    unfold Papers.P2.Gap.BooleanSubLattice.symmDiff
    simpa using (Set.finite_singleton (0 : ℕ))
end

section
  variable (A B C : Set ℕ)

  example : (⟦A⟧ᵇ ⊔ᵇ ⟦B⟧ᵇ) = ⟦A ∪ B⟧ᵇ := by simp
  example : (⟦A⟧ᵇ ⊓ᵇ ⟦B⟧ᵇ) = ⟦A ∩ B⟧ᵇ := by simp
  example : ᶜᵇ ⟦A⟧ᵇ = ⟦Aᶜ⟧ᵇ := by simp

  -- congruence check
  example (h : (Papers.P2.Gap.BooleanSubLattice.symmDiff A B).Finite) :
      (⟦A⟧ᵇ ⊔ᵇ ⟦C⟧ᵇ) = (⟦B⟧ᵇ ⊔ᵇ ⟦C⟧ᵇ) := by
    -- use simp to reduce to the mk case
    simp only [bUnion_mk]
    apply Quot.sound
    -- from (A △ B) finite, also (A∪C △ B∪C) finite:
    have hEq :
      Papers.P2.Gap.BooleanSubLattice.symmDiff (A ∪ C) (B ∪ C)
        = Papers.P2.Gap.BooleanSubLattice.symmDiff A B \ C := by
      -- your code already has the "right argument fixed" lemma;
      -- we just commute unions to match it
      simpa [Set.union_comm] using
        (Papers.P2.Gap.BooleanSubLattice.symmDiff_union_right_eq A B C)
    
    -- finite because it's a subset of (A △ B)
    have hfin : (Papers.P2.Gap.BooleanSubLattice.symmDiff (A ∪ C) (B ∪ C)).Finite := by
      have : (Papers.P2.Gap.BooleanSubLattice.symmDiff A B \ C).Finite :=
        h.subset (by intro x hx; exact hx.1)
      simpa [hEq] using this
    
    exact (by simpa [Papers.P2.Gap.BooleanSubLattice.FinSymmDiffRel] using hfin)
end

section
  variable (A B : Set ℕ)

  -- domain-side ops
  example : (⟦A⟧ᵇ ⊔ᵇ ⟦B⟧ᵇ) = ⟦A ∪ B⟧ᵇ := by simp
  example : (⟦A⟧ᵇ ⊓ᵇ ⟦B⟧ᵇ) = ⟦A ∩ B⟧ᵇ := by simp
  example : ᶜᵇ ⟦A⟧ᵇ = ⟦Aᶜ⟧ᵇ := by simp

  -- homomorphism laws for ῑ
  example : qSup (iotaBar ⟦A⟧ᵇ) (iotaBar ⟦B⟧ᵇ) = iotaBar ⟦A ∪ B⟧ᵇ := by simp
  example : qInf (iotaBar ⟦A⟧ᵇ) (iotaBar ⟦B⟧ᵇ) = iotaBar ⟦A ∩ B⟧ᵇ := by simp
  example : qCompl (iotaBar ⟦A⟧ᵇ) = iotaBar ⟦Aᶜ⟧ᵇ := by simp
end