/-
  Paper 45: Weight-Monodromy Conjecture — Lean 4 Formalization
  C1_Polarization.lean: Theorem C1 — Polarization Forces Degeneration in BISH

  Main result (Theorem C1):
    polarization_forces_degeneration_BISH :
      PolarizedComplex -> Laplacian = 0 -> d = 0

  The positive-definite inner product provides a COMPUTATIONAL BYPASS:
  from ‖dx‖² + ‖d†x‖² = 0 and norm non-negativity,
  we deduce dx = 0 equationally — no omniscience needed.

  This is why Kashiwara's theorem works over ℂ (where positive-definite
  metrics exist in all dimensions) but fails over ℚ_p (Theorem C3).

  Proof:
    1. Laplacian = d∘d† + d†∘d = 0
    2. ‖d† x‖² = re ⟪(d†† ∘ d†) x, x⟫ = re ⟪(d ∘ d†) x, x⟫
    3. ‖d x‖² = re ⟪(d† ∘ d) x, x⟫
    4. Sum = re ⟪(d∘d† + d†∘d) x, x⟫ = re ⟪0, x⟫ = 0
    5. Both terms ≥ 0 (sq_nonneg), so ‖d x‖ = 0, so d x = 0.
    6. ContinuousLinearMap.ext: d = 0.

  Axiom profile: propext, Classical.choice, Quot.sound (Mathlib ℝ/ℂ infrastructure).
  No sorry. No custom axioms. FULL PROOF.
-/

import Papers.P45_WMC.Defs

noncomputable section

namespace Papers.P45

open ContinuousLinearMap

/-- **Theorem C1 (Polarization Forces Degeneration in BISH).**
    Given a polarized complex (V, d, ⟪·,·⟫) where the Hodge Laplacian
    Δ = d∘d† + d†∘d vanishes, the differential d must be zero.

    The positive-definite metric converts a decidability question
    ("is d = 0?") into an equational identity ("‖dx‖ = 0 for all x,
    therefore d = 0"). No omniscience principle is needed.

    This is a BISH result: the proof is constructive given the
    polarization data. The constructive content is that positive-
    definiteness provides a COMPUTATIONAL BYPASS around LPO. -/
theorem polarization_forces_degeneration_BISH
    (C : PolarizedComplex)
    (h_laplacian : C.laplacian = 0) :
    C.d = 0 := by
  -- Goal: show d = 0 by showing d x = 0 for all x.
  ext x
  rw [zero_apply]
  -- It suffices to show ‖d x‖ = 0.
  rw [← norm_eq_zero]
  -- ‖d x‖ = 0 iff ‖d x‖² = 0 (since ‖d x‖ ≥ 0)
  nlinarith [norm_nonneg (C.d x), sq_nonneg ‖C.d x‖,
    -- Key chain: ‖d x‖² + ‖d† x‖² = 0
    -- Step 1: ‖d x‖² = re ⟪(d† ∘L d) x, x⟫
    apply_norm_sq_eq_inner_adjoint_left C.d x,
    -- Step 2: ‖d† x‖² = re ⟪(d ∘L d†) x, x⟫  (using d†† = d)
    show ‖(adjoint C.d) x‖ ^ 2 =
      RCLike.re (inner (𝕜 := ℂ) ((C.d.comp (adjoint C.d)) x) x) from by
      have := apply_norm_sq_eq_inner_adjoint_left (adjoint C.d) x
      rwa [adjoint_adjoint] at this,
    -- Step 3: ‖d† x‖² ≥ 0
    sq_nonneg ‖(adjoint C.d) x‖,
    -- Step 4: re ⟪(d∘d† + d†∘d) x, x⟫ = 0 (from Laplacian = 0)
    show RCLike.re (inner (𝕜 := ℂ) ((C.d.comp (adjoint C.d) + (adjoint C.d).comp C.d) x) x) = 0 from by
      have : C.d.comp (adjoint C.d) + (adjoint C.d).comp C.d = C.laplacian := rfl
      rw [this, h_laplacian, zero_apply, inner_zero_left, map_zero],
    -- Step 5: re ⟪(A + B) x, x⟫ = re ⟪A x, x⟫ + re ⟪B x, x⟫
    show RCLike.re (inner (𝕜 := ℂ) ((C.d.comp (adjoint C.d) + (adjoint C.d).comp C.d) x) x) =
      RCLike.re (inner (𝕜 := ℂ) ((C.d.comp (adjoint C.d)) x) x) +
      RCLike.re (inner (𝕜 := ℂ) (((adjoint C.d).comp C.d) x) x) from by
      rw [add_apply, inner_add_left, map_add]]

end Papers.P45
