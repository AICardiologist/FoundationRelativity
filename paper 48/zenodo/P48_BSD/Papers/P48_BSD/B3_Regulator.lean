/-
  Paper 48: BSD Conjecture — Constructive Calibration
  B3_Regulator.lean: Theorem B3 — Regulator is strictly positive (BISH)

  Main result:
  - regulator_positive: regulator r > 0

  The regulator is the determinant of the positive-definite Néron-Tate
  matrix. Positive-definiteness implies det > 0 (all eigenvalues > 0).
  This is a BISH result: no omniscience principle is needed.

  Proof uses Mathlib's Matrix.PosDef.det_pos.

  No custom axioms beyond Defs.lean. No sorry.
-/

import Papers.P48_BSD.Defs

noncomputable section

namespace Papers.P48

/-- **Theorem B3 (Regulator Positivity).**
    The regulator Reg_E = det(⟨Pᵢ, Pⱼ⟩) is strictly positive.

    Proof: A positive-definite matrix has all eigenvalues > 0,
    and det = product of eigenvalues > 0.

    This is a BISH result: positive-definiteness is the Archimedean
    axiom (from geometry), and det > 0 follows by linear algebra.
    No LPO or other omniscience principle is needed.

    Key contrast with B1: the regulator is computable AND nonzero,
    while L^(r)(E,1) is computable but zero-testing requires LPO.
    The BSD formula equates a computable-but-undecidable quantity
    with computable-and-decidable quantities. -/
theorem regulator_positive (r : ℕ) : regulator r > 0 :=
  (neron_tate_pos_def r).det_pos

/-- The regulator is nonzero (immediate corollary). -/
theorem regulator_ne_zero (r : ℕ) : regulator r ≠ 0 :=
  ne_of_gt (regulator_positive r)

end Papers.P48
