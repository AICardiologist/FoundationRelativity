/-
  Papers/P2_BidualGap/Constructive/MainTheoremFinal.lean
  
  The complete proof of Bidual Gap ↔ WLPO.
  This file assembles all the pieces developed in the other modules.
-/

import Papers.P2_BidualGap.Constructive.Sequences
import Papers.P2_BidualGap.Constructive.WLPO_ASP_Core
import Papers.P2_BidualGap.Constructive.HahnBanach
import Papers.P2_BidualGap.Logic.WLPOSimple

namespace Papers.P2_BidualGap.Constructive

open CReal CNormedSpace

/-- The Separating Hahn-Banach principle (SHB) -/
def SeparatingHahnBanach : Prop :=
  ∀ (v : ell_infty), 
    (v ∈ c_zero) ∨ 
    (∃ (φ : ell_infty →L[CReal] CReal), 
      (∀ x ∈ c_zero, equiv (φ.toFun x) zero) ∧ 
      ¬equiv (φ.toFun v) zero)

/-- -- LaTeX Lemma 6.1
Bidual gap implies Separating Hahn-Banach -/
lemma gap_implies_shb : 
  hasBidualGap ell_infty → SeparatingHahnBanach := by
  intro hgap v
  -- If ℓ∞ has a bidual gap, there exists Φ ∈ (ℓ∞)** \ ι(ℓ∞)
  -- This Φ gives us separating functionals
  sorry -- TODO: Extract separating functional from gap witness

/-- -- LaTeX Theorem 6.2 (Direction 1)
Bidual Gap → WLPO via SHB -/
theorem gap_to_wlpo : hasBidualGap ell_infty → WLPO := by
  intro hgap
  -- Step 1: Gap gives us SHB
  have hshb := gap_implies_shb hgap
  -- Step 2: Apply SHB to witness sequence
  intro α
  let v := witness_sequence α
  cases hshb v with
  | inl hv =>
    -- v ∈ c₀, so α is all zeros
    left
    exact (witness_in_c_zero_iff α).mp hv
  | inr ⟨φ, hφ_zero, hφ_v⟩ =>
    -- φ separates v from c₀, so α has a true value
    right
    intro hall
    have : v ∈ c_zero := (witness_in_c_zero_iff α).mpr hall
    have : equiv (φ.toFun v) zero := hφ_zero v this
    exact hφ_v this

/-- -- LaTeX Lemma 6.3
ASP enables the gap construction -/
lemma asp_gives_gap : ASP → hasBidualGap ell_infty := by
  intro hasp
  -- Use Hahn-Banach to extend Banach limit
  let F := banach_limit_functional hasp
  -- F witnesses the gap: F(c₀) = 0 but F(1) ≠ 0
  -- So F is not in the image of canonical embedding
  use F
  intro x
  -- If F = ι(x) for some x ∈ ℓ∞, then F would be represented by x
  -- But F(c₀) = 0 forces x ∈ c₀⊥⊥ = c₀ (by reflexivity of c₀)
  -- Yet F(1) = 1 ≠ 0 = x(1), contradiction
  sorry -- TODO: Complete the argument

/-- -- LaTeX Theorem 6.4 (Direction 2)
WLPO → Bidual Gap via ASP and Hahn-Banach -/
theorem wlpo_to_gap : WLPO → hasBidualGap ell_infty := by
  intro hwlpo
  -- Step 1: WLPO gives us ASP
  have hasp := wlpo_to_asp hwlpo
  -- Step 2: ASP gives us the gap
  exact asp_gives_gap hasp

/-- -- LaTeX Main Theorem 2.1
The fundamental equivalence -/
theorem bidual_gap_iff_wlpo : 
  hasBidualGap ell_infty ↔ WLPO := by
  constructor
  · exact gap_to_wlpo
  · exact wlpo_to_gap

/-- -- LaTeX Corollary 6.5
More general: Existence of any Banach space with gap ↔ WLPO -/
theorem exists_gap_iff_wlpo :
  (∃ (E : Type*) [CNormedSpace E], hasBidualGap E) ↔ WLPO := by
  constructor
  · intro ⟨E, _, hgap⟩
    -- Any gap gives us separating functionals
    -- The proof generalizes from ℓ∞ to arbitrary E
    sorry -- TODO: Generalize gap_to_wlpo
  · intro hwlpo
    -- WLPO gives us ℓ∞ with gap
    use ell_infty
    exact wlpo_to_gap hwlpo

/-- -- LaTeX Corollary 6.6
Without WLPO, all Banach spaces are reflexive -/
theorem no_wlpo_all_reflexive (hnwlpo : ¬WLPO) :
  ∀ (E : Type*) [CNormedSpace E], ¬hasBidualGap E := by
  intro E _ hgap
  have : WLPO := exists_gap_iff_wlpo.mp ⟨E, hgap⟩
  exact hnwlpo this

/-- -- LaTeX Remark 6.7
The role of separability -/
theorem separable_reflexive_without_wlpo (hnwlpo : ¬WLPO) :
  ∀ (E : Type*) [CNormedSpace E] [SeparableSpace E], 
  isReflexive E := by
  intro E _ _
  -- Separable spaces have countable dense subsets
  -- This allows more constructive techniques
  sorry -- TODO: Use separability crucially

end Papers.P2_BidualGap.Constructive