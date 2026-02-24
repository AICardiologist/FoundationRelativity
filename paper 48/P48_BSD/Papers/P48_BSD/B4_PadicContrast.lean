/-
  Paper 48: BSD Conjecture — Constructive Calibration
  B4_PadicContrast.lean: Theorem B4 — p-adic Height Not Positive-Definite

  Main result:
  - padic_height_not_pos_def: For r ≥ 5, the p-adic height pairing
    cannot be positive-definite (anisotropic).

  This is the p-adic counterpart to B2. The Archimedean height IS
  positive-definite (B2), but the p-adic height is NOT (B4).
  This contrast explains exceptional zero phenomena in p-adic BSD
  (Mazur-Tate-Teitelbaum).

  Reuses Paper 45 C3 methodology (u-invariant obstruction).

  No custom axioms beyond Defs.lean. No sorry.
-/

import Papers.P48_BSD.Defs

noncomputable section

namespace Papers.P48

-- ============================================================
-- §1. p-adic Height Not Positive-Definite
-- ============================================================

/-- **Theorem B4 (p-adic Height Not Positive-Definite).**
    For algebraic rank r ≥ 5, the p-adic height pairing has an
    isotropic vector (nonzero v with B(v,v) = 0), so it cannot
    be positive-definite (anisotropic).

    This follows from u(ℚ_p) = 4: any symmetric bilinear form
    of dimension ≥ 5 over ℚ_p is isotropic.

    Consequence: the p-adic regulator CAN vanish, creating the
    exceptional zero phenomenon that requires the ℒ-invariant
    correction of Mazur-Tate-Teitelbaum. -/
theorem padic_height_not_pos_def
    (r : ℕ) (hr : r ≥ 5)
    (h_symm : ∀ i j : Fin r, padic_height r i j = padic_height r j i) :
    ¬ (∀ (v : Fin r → Q_p), v ≠ 0 →
      ∑ i, ∑ j, v i * padic_height r i j * v j ≠ 0) := by
  intro hpd
  -- By padic_form_isotropic: for dim ≥ 5, any symmetric form is isotropic
  obtain ⟨v, hv_ne, hv_zero⟩ := padic_form_isotropic r hr (padic_height r) h_symm
  -- v ≠ 0 and ∑ᵢⱼ vᵢ · h(i,j) · vⱼ = 0
  -- But hpd says this sum ≠ 0 for all nonzero v
  exact absurd hv_zero (hpd v hv_ne)

-- ============================================================
-- §2. Archimedean vs p-adic Contrast
-- ============================================================

/-- The Archimedean and p-adic cases are fundamentally different.
    - Archimedean (B2): Néron-Tate IS positive-definite → regulator > 0
    - p-adic (B4): height pairing NOT positive-definite for rank ≥ 5

    This gap is the constructive content of the exceptional zero
    phenomenon. Classical BSD works because the Archimedean polarization
    is AVAILABLE. p-adic BSD has pathologies because it is NOT. -/
theorem archimedean_padic_contrast (r : ℕ) (hr : r ≥ 5)
    (h_symm : ∀ i j : Fin r, padic_height r i j = padic_height r j i) :
    -- Archimedean: positive-definite (from axiom)
    (neron_tate_matrix r).PosDef ∧
    -- p-adic: NOT positive-definite
    ¬ (∀ (v : Fin r → Q_p), v ≠ 0 →
      ∑ i, ∑ j, v i * padic_height r i j * v j ≠ 0) :=
  ⟨neron_tate_pos_def r, padic_height_not_pos_def r hr h_symm⟩

end Papers.P48
