/-
  Paper 21: Bell Nonlocality and the Constructive Cost of Disjunction: LLPO
  Main/Stratification.lean — Three-level stratification theorem

  Bell's theorem exhibits observable-dependent logical cost:
    Level 1 (BISH): CHSH bound and quantum violation are computable
    Level 2 (LLPO): The disjunctive Bell conclusion ↔ LLPO
    Level 3 (Hierarchy): WLPO → LLPO (strict hierarchy)
-/
import Papers.P21_BellLLPO.PartA.PartA_Main
import Papers.P21_BellLLPO.PartB.PartB_Main

namespace Papers.P21

/-- The three-level stratification of Bell's theorem:
    1. (BISH) CHSH bound holds for all LHV assignments
    2. (LLPO) The disjunctive Bell conclusion is equivalent to LLPO
    3. (Hierarchy) WLPO → LLPO (strict hierarchy) -/
theorem bell_stratification :
    -- Level 1: BISH (CHSH bound)
    (∀ (m : LHVAssignment), |chshExpr m| ≤ 2) ∧
    -- Level 2: LLPO equivalence
    (LLPO ↔ BellSignDecision) ∧
    -- Level 3: Hierarchy (WLPO → LLPO)
    (WLPO → LLPO) :=
  ⟨chsh_abs_bound, llpo_iff_bell_sign, wlpo_implies_llpo⟩

-- ============================================================
-- Axiom audit
-- Expected: [propext, Classical.choice, Quot.sound, llpo_real_of_llpo]
-- ============================================================
#print axioms bell_stratification

end Papers.P21
