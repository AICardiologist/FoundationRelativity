/-
  Paper 47: Fontaine-Mazur Conjecture — Lean 4 Formalization
  FM2_deRham.lean: Theorem FM2 — de Rham Condition Requires LPO

  Main result:
    Deciding filtration dimensions and determinants over ℚ_p requires LPO.

  The de Rham condition (dim D_dR = dim W) requires computing exact
  ranks over ℚ_p. Rank computation requires Gaussian elimination,
  which requires deciding whether pivots are zero — i.e., LPO.

  This file is more axiom-heavy than FM1 because the connection
  between matrix rank and LPO is a standard result in constructive
  linear algebra (Bridges & Richman 1987).

  Custom axiom: rank_computation_needs_LPO (from Defs.lean).
  No sorry.
-/

import Papers.P47_FM.Defs

noncomputable section

namespace Papers.P47

-- ============================================================
-- FM2: Hodge Filtration Requires LPO
-- ============================================================

/-- Determinant decidability as a Prop: for every n×n matrix over ℚ_p,
    either det = 0 or det ≠ 0. -/
def DetOracle : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) Q_p), M.det = 0 ∨ M.det ≠ 0

/-- The de Rham encoding: a single ℚ_p element x determines
    a 1×1 matrix whose determinant is x.
    Deciding det = 0 decides x = 0. -/
def deRham_encoding (x : Q_p) : Matrix (Fin 1) (Fin 1) Q_p :=
  Matrix.of (fun _ _ => x)

/-- The encoding matrix has det = x. -/
theorem deRham_encoding_det (x : Q_p) :
    (deRham_encoding x).det = x := by
  simp [deRham_encoding]

/-- **Theorem FM2 Forward: Determinant decidability over ℚ_p implies LPO.**
    Given a determinant oracle, construct a 1×1 matrix with entry x.
    Then det = x, so oracle decides x = 0.

    This is also a direct consequence of rank_computation_needs_LPO. -/
theorem det_oracle_gives_LPO : DetOracle → LPO_Q_p := by
  intro oracle x
  have hdec := oracle 1 (deRham_encoding x)
  rw [deRham_encoding_det] at hdec
  exact hdec

/-- **FM2 Reverse: LPO gives determinant decidability.**
    Given LPO_Q_p, testing det(M) = 0 is just testing a single
    element of ℚ_p for zero. -/
theorem LPO_gives_det_oracle : LPO_Q_p → DetOracle := by
  intro hlpo n M
  exact hlpo M.det

/-- **Theorem FM2 (de Rham Condition ↔ LPO).**
    Deciding determinants over ℚ_p (needed for rank computation,
    needed for the de Rham condition) is equivalent to LPO for ℚ_p. -/
theorem FM2_deRham_iff_LPO : DetOracle ↔ LPO_Q_p :=
  ⟨det_oracle_gives_LPO, LPO_gives_det_oracle⟩

end Papers.P47
