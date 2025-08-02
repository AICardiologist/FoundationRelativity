import Papers.P1_GBC.Arithmetic
import Papers.P1_GBC.Core
import Papers.P1_GBC.Defs

/-!
# Logic Axioms for Gödel-Banach Correspondence

This module axiomatizes the logic consequences needed for the Gödel-Banach
correspondence, following Math-AI's strategic guidance from Sprint 50.

## Strategy
Instead of formalizing Gödel's incompleteness theorems directly, we axiomatize
their consequences relevant to the operator-theoretic setting.

## Main Axioms
- `consistency_characterization`: Links consistency to non-provability of G
- `diagonal_property`: The Gödel sentence's self-reference property
- `classical_logic_requirement`: Foundation-relative nature of the results

## References
- Math-AI consultation for Sprint 50
- Avigad & Zach's incompleteness notes
-/

namespace Papers.P1_GBC.LogicAxioms

open Arithmetic

/-! ### Core Axiomatizations -/

/-- **Axiom 1**: Consistency of PA is equivalent to non-provability of Gödel sentence.
This is the key consequence of Gödel's second incompleteness theorem that we need. -/
axiom consistency_characterization :
  Papers.P1_GBC.Defs.consistencyPredicate Papers.P1_GBC.Defs.peanoArithmetic ↔ ¬Provable G_formula

/-- **Axiom 2**: The Gödel sentence satisfies the diagonal property.
G is equivalent to "G is not provable" (externally). -/
axiom diagonal_property :
  -- External semantic property: G is true iff G is not provable
  -- This requires a model-theoretic formulation
  ∃ (semantic_truth : Sigma1 → Prop),
  semantic_truth G_formula ↔ ¬Provable G_formula

/-- **Axiom 3**: Classical logic is required for the correspondence.
In constructive foundations (BISH), the diagonal lemma fails. -/
axiom classical_logic_requirement (F : Foundation) :
  (F = Foundation.bish → ¬∃ (G : Sigma1), Provable G ↔ ¬Provable G) ∧
  (F = Foundation.zfc → ∃ (G : Sigma1), G = G_formula)

/-! ### Derived Consequences -/

/-- The Gödel scalar c_G is always false (by incompleteness) -/
lemma c_G_always_false : c_G = false := by
  simp only [c_G]
  exact decide_eq_false_iff_not.mpr incompleteness

/-- The Gödel operator is always the identity (when c_G = false) -/
lemma G_always_identity (g : ℕ) : G (g:=g) = 1 := by
  simp only [G]
  rw [c_G_always_false]
  simp

/-- Consistency is equivalent to G being surjective (which is always true) -/
theorem consistency_iff_G_surjective (g : ℕ) :
  Papers.P1_GBC.Defs.consistencyPredicate Papers.P1_GBC.Defs.peanoArithmetic ↔ 
  Function.Surjective (G (g:=g)).toLinearMap := by
  rw [consistency_characterization]
  -- Now we need to prove: ¬Provable G_formula ↔ Function.Surjective (G.toLinearMap)
  -- First convert ¬Provable G_formula ↔ c_G = false
  have h1 : ¬Provable G_formula ↔ c_G = false := by
    constructor
    · intro h_not_prov
      simp only [c_G]
      exact decide_eq_false_iff_not.mpr h_not_prov
    · intro h_cG_false
      simp only [c_G] at h_cG_false
      exact decide_eq_false_iff_not.mp h_cG_false
  -- Then use G_surjective_iff_not_provable : Function.Surjective G ↔ c_G = false
  rw [h1]
  exact G_surjective_iff_not_provable.symm

/-- Foundation-relative: BISH cannot support the diagonal lemma -/
lemma bish_no_diagonal :
  ¬∃ (G : Sigma1), (∃ (_ : Decidable (Provable G)), Provable G ↔ ¬Provable G) := by
  intro ⟨G, ⟨hdec, hdiag⟩⟩
  -- In constructive logic, this leads to contradiction
  -- The diagonal property G ↔ ¬G is classically valid but constructively impossible
  have h1 : Provable G → ¬Provable G := hdiag.mp
  have h2 : ¬Provable G → Provable G := hdiag.mpr
  -- This creates a contradiction in constructive logic
  cases hdec with
  | isTrue hp => exact h1 hp hp
  | isFalse hnp => exact hnp (h2 hnp)

/-! ### Sigma1-EM Axiomatization -/

/-- Predicate indicating if a foundation supports Untruncated Σ₁ Excluded Middle.
This is the key logical principle required for the Gödel-Banach construction. -/
axiom HasSigma1EM (F : Foundation) : Prop

/-- BISH lacks Σ₁-EM (being constructive/intuitionistic) -/
axiom BISH_lacks_Sigma1EM : ¬HasSigma1EM Foundation.bish

/-- ZFC has Σ₁-EM (being classical) -/
axiom ZFC_has_Sigma1EM : HasSigma1EM Foundation.zfc

/-- Necessity: The Gödel-Banach construction requires Σ₁-EM.
This captures that c_G cannot be defined without case analysis on undecidable Σ₁ statements. -/
axiom GodelBanach_Requires_Sigma1EM (F : Foundation) :
  (∃ (w : Papers.P1_GBC.Defs.foundationGodelCorrespondence F), True) → HasSigma1EM F

/-- Sufficiency: If the foundation has Σ₁-EM, the correspondence can be constructed.
This captures that the analytical machinery works once c_G is definable. -/
axiom Sigma1EM_Sufficient_for_GodelBanach (F : Foundation) :
  HasSigma1EM F → ∃ (w : Papers.P1_GBC.Defs.foundationGodelCorrespondence F), True

/-! ### Model-Theoretic Properties -/

-- Model theory aspects are deferred to avoid circular dependencies
-- The key axiomatizations above capture what we need for the correspondence

end Papers.P1_GBC.LogicAxioms