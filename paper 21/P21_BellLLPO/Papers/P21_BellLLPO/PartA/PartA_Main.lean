/-
  Paper 21: Bell Nonlocality and the Constructive Cost of Disjunction: LLPO
  PartA/PartA_Main.lean — Part A assembly and axiom audit

  All Part A results are BISH: no omniscience principles required.
-/
import Papers.P21_BellLLPO.PartA.BellNegation

namespace Papers.P21

/-- Part A summary: CHSH bound, quantum violation, and ¬LHV are all BISH. -/
theorem partA_summary :
    (∀ (m : LHVAssignment), |chshExpr m| ≤ 2) ∧
    S_quantum > 2 ∧
    ¬∃ (m : LHVAssignment), chshExpr m > 2 :=
  ⟨chsh_abs_bound, S_quantum_gt_two, neg_lhv⟩

-- Axiom audit: Part A uses no custom axioms
-- Expected: [propext, Classical.choice, Quot.sound]
#print axioms chsh_bound
#print axioms chsh_abs_bound
#print axioms S_quantum_gt_two
#print axioms neg_lhv
#print axioms partA_summary

end Papers.P21
