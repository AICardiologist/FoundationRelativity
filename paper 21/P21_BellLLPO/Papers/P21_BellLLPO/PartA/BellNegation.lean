/-
  Paper 21: Bell Nonlocality and the Constructive Cost of Disjunction: LLPO
  PartA/BellNegation.lean — ¬LHV conclusion (BISH)

  No local hidden variable model can reproduce the quantum violation:
  the CHSH bound forces |S| ≤ 2, but quantum mechanics gives S > 2.
-/
import Papers.P21_BellLLPO.PartA.CHSHBound
import Papers.P21_BellLLPO.PartA.QuantumViolation

namespace Papers.P21

/-- Theorem 3 (Bell's Theorem, negation form):
    No deterministic LHV assignment achieves S > 2.
    This is BISH — a finite contradiction. -/
theorem neg_lhv : ¬∃ (m : LHVAssignment), chshExpr m > 2 := by
  intro ⟨m, hm⟩
  have hbound := chsh_abs_bound m
  have : chshExpr m ≤ |chshExpr m| := le_abs_self _
  linarith

end Papers.P21
