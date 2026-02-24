/-
  Paper 48: BSD Conjecture — Constructive Calibration
  B2_Polarization.lean: Theorem B2 — Néron-Tate as Archimedean Polarization

  Main results:
  - archimedean_polarization_pos_def: Néron-Tate matrix is PosDef
  - neron_tate_inner_product_space: InnerProductSpace on ℝ^r from matrix
  - height_positive: diagonal entries (self-pairings) are strictly positive

  The Archimedean polarization (Néron-Tate height) provides a positive-
  definite inner product on E(ℚ) ⊗ ℝ ≅ ℝ^r. This is AVAILABLE because
  u(ℝ) = 1. Contrast with B4 where u(ℚ_p) = 4 blocks this.

  No custom axioms beyond Defs.lean. No sorry.
-/

import Papers.P48_BSD.Defs

noncomputable section

namespace Papers.P48

open Matrix

-- ============================================================
-- §1. Positive-Definiteness
-- ============================================================

/-- The Néron-Tate matrix is positive-definite (from axiom).
    This is the Archimedean polarization of BSD. -/
theorem archimedean_polarization_pos_def (r : ℕ) :
    (neron_tate_matrix r).PosDef :=
  neron_tate_pos_def r

/-- The Néron-Tate matrix is symmetric (derived from PosDef). -/
theorem neron_tate_is_hermitian (r : ℕ) :
    (neron_tate_matrix r).IsHermitian :=
  (neron_tate_pos_def r).isHermitian

-- ============================================================
-- §2. Inner Product Space Construction
-- ============================================================

/-- The Néron-Tate matrix induces an inner product on ℝ^r.
    This IS the Archimedean polarization of BSD.
    Uses Mathlib's Matrix.toInnerProductSpace. -/
def neron_tate_inner_product_space (r : ℕ) :
    @InnerProductSpace ℝ (Fin r → ℝ) _
      ((neron_tate_matrix r).toSeminormedAddCommGroup
        (neron_tate_pos_def r).posSemidef) :=
  (neron_tate_matrix r).toInnerProductSpace (neron_tate_pos_def r).posSemidef

-- ============================================================
-- §3. Diagonal Positivity (Height > 0)
-- ============================================================

/-- Each diagonal entry ĥ(Pᵢ, Pᵢ) > 0.
    This is the Néron-Tate height of a generator, which is
    strictly positive for non-torsion points.
    Consequence: non-torsion points are detectable — the condition
    ĥ(P) > 0 is semi-decidable (open in ℝ, can be verified
    to any finite precision). -/
theorem height_positive (r : ℕ) (i : Fin r) :
    0 < (neron_tate_matrix r) i i :=
  (neron_tate_pos_def r).diag_pos

end Papers.P48
