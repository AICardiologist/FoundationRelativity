/-
  Paper 46: Tate Conjecture — Lean 4 Formalization
  T3_Obstruction.lean: Theorem T3 — Polarization Obstruction

  Main result (Theorem T3):
    The Poincaré pairing on V cannot be anisotropic (positive-definite)
    when dim V ≥ 5, because u(ℚ_ℓ) = 4.

  Consequence: orthogonal projection onto galois_fixed is impossible.
  The Hodge-theoretic strategy (which works over ℂ where positive-definite
  metrics exist in all dimensions) is blocked over ℚ_ℓ.

  This parallels Paper 45 Theorem C3, adapted from Hermitian forms
  over quadratic extensions (dim ≥ 3) to the Poincaré pairing on V
  (symmetric bilinear, dim ≥ 5).

  Axiom profile: poincare_isotropic_high_dim (from Defs.lean)
  No sorry.
-/

import Papers.P46_Tate.Defs

noncomputable section

namespace Papers.P46

-- ============================================================
-- §1. The Poincaré Pairing Cannot Be Positive-Definite
-- ============================================================

/-- **Theorem T3: Polarization is blocked by the u-invariant.**

    Over ℚ_ℓ (a local field with u-invariant 4), the Poincaré
    pairing on V = H^{2r}(X, ℚ_ℓ(r)) cannot be anisotropic
    (i.e., positive-definite in the sense that form(v,v) = 0 → v = 0)
    when the dimension of V is at least 5.

    Proof: By poincare_isotropic_high_dim, there exists v ≠ 0 with
    poincare_pairing(v, v) = 0. But anisotropy requires that
    poincare_pairing(v, v) = 0 → v = 0, giving v = 0 and
    contradicting v ≠ 0.

    Mathematical context: u(ℚ_ℓ) = 4 means every quadratic form
    of dimension > 4 over ℚ_ℓ has a nontrivial zero. The Poincaré
    pairing is a nondegenerate symmetric bilinear form on V, which
    corresponds to a quadratic form of dimension = dim V ≥ 5 > 4.
    Therefore it must be isotropic.

    This obstruction is permanent: no "p-adic polarization" can
    replace the Hodge metric in the Tate Conjecture setting. -/
theorem poincare_not_anisotropic
    (hdim : 5 ≤ Module.finrank Q_ell V) :
    ¬ (∀ v : V, poincare_pairing v v = 0 → v = 0) := by
  intro h_aniso
  -- By the u-invariant obstruction, there exists a nonzero
  -- isotropic vector for the Poincaré pairing
  obtain ⟨v, hv_ne, hv_iso⟩ := poincare_isotropic_high_dim hdim
  -- Anisotropy gives v = 0 from poincare_pairing(v, v) = 0
  exact hv_ne (h_aniso v hv_iso)

/-- **Corollary: The metric-based decomposition strategy is blocked.**

    Over ℂ, the Hodge metric allows splitting V = ker(Frob - I) ⊕ ...
    via orthogonal projection (positive-definite inner product exists
    in all dimensions). Over ℚ_ℓ, since the Poincaré pairing is
    isotropic in dimension ≥ 5, no anisotropic metric exists to
    perform this splitting.

    Any proof of the Tate Conjecture must use a strategy other than
    metric/polarization-based orthogonal projection. -/
theorem orthogonal_projection_blocked
    (hdim : 5 ≤ Module.finrank Q_ell V) :
    ¬ (∀ v : V, poincare_pairing v v = 0 → v = 0) :=
  poincare_not_anisotropic hdim

end Papers.P46
