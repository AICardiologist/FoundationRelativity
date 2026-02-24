/-
  Paper 21: Bell Nonlocality and the Constructive Cost of Disjunction: LLPO
  PartA/CHSHBound.lean — The CHSH bound (BISH)

  For any deterministic assignment (a₁, a₂, b₁, b₂) ∈ {±1}⁴,
  the CHSH expression a₁b₁ + a₁b₂ + a₂b₁ - a₂b₂ ∈ {-2, +2}.
  This is a pure finite case analysis (16 cases), entirely BISH.
-/
import Papers.P21_BellLLPO.Defs.CHSH

namespace Papers.P21

/-- Theorem 1: The CHSH expression for any deterministic ±1 assignment
    equals ±2. Proof by exhaustive case analysis (16 cases). -/
theorem chsh_bound (m : LHVAssignment) :
    chshExpr m = 2 ∨ chshExpr m = -2 := by
  obtain ⟨a₁, a₂, b₁, b₂, ha₁, ha₂, hb₁, hb₂⟩ := m
  simp only [chshExpr]
  rcases ha₁ with rfl | rfl <;> rcases ha₂ with rfl | rfl <;>
  rcases hb₁ with rfl | rfl <;> rcases hb₂ with rfl | rfl <;>
  norm_num

/-- The absolute value of the CHSH expression is at most 2. -/
theorem chsh_abs_bound (m : LHVAssignment) :
    |chshExpr m| ≤ 2 := by
  rcases chsh_bound m with h | h <;> rw [h] <;> norm_num

end Papers.P21
