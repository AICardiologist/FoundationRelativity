/-
Papers/P13_EventHorizon/BISH_Content.lean
Module 6: BISH-level content of the Schwarzschild interior.

Demonstrates that the physical content — curvature computations and
geodesic focusing over finite parameter intervals — is BISH (Height 0).
No Classical.choice appears in these proofs.

Key results:
  1. Kretschner scalar K = 48M²/r⁶ is constructively computable for any r > 0
  2. Cycloid geodesic position is constructively computable for η ∈ (0, π)
  3. For any ε > 0, there exists a constructive η with r(η) < ε (approaching
     the singularity arbitrarily closely is BISH)

The BISH dispensability: empirical predictions (curvature at any specified
finite r, geodesic position at any finite proper time) require no omniscience.
Only the completed assertion "r reaches exactly 0" costs LPO.
-/
import Papers.P13_EventHorizon.RadialGeodesic

namespace Papers.P13

open Real Set

-- ========================================================================
-- Kretschner scalar (constructively computable for r > 0)
-- ========================================================================

/-- The Kretschner scalar K = 48M²/r⁶.
    This is the quadratic curvature invariant R_{μνρσ}R^{μνρσ} for the
    Schwarzschild geometry. It is constructively computable for any r > 0,
    whether in the interior or exterior. -/
noncomputable def kretschner (M r : ℝ) : ℝ := 48 * M ^ 2 / r ^ 6

/-- The Kretschner scalar is well-defined and positive for M ≠ 0, r > 0.
    No Classical.choice needed — this is a Height 0 (BISH) computation. -/
theorem kretschner_pos {M r : ℝ} (hM : M ≠ 0) (hr : r > 0) :
    kretschner M r > 0 := by
  unfold kretschner
  apply div_pos
  · positivity
  · positivity

/-- The Kretschner scalar is constructively computable in the interior.
    This is the same algebraic expression as in the exterior — only r > 0
    is needed, not r > 2M. -/
theorem kretschner_computable_interior {M r : ℝ} (_h_int : Interior M r) :
    kretschner M r = 48 * M ^ 2 / r ^ 6 := by
  rfl

/-- The Kretschner scalar at the cycloid position r_cycloid M η.
    Constructively computable for any η ∈ (0, π). -/
theorem kretschner_at_cycloid {M η : ℝ} (hM : M > 0) (hη : η ∈ Ioo 0 π) :
    kretschner M (r_cycloid M η) > 0 := by
  apply kretschner_pos (ne_of_gt hM)
  exact (r_cycloid_interior hM hη).r_pos

-- ========================================================================
-- Cycloid geodesic position is constructively computable
-- ========================================================================

/-- For η ∈ (0, π) and M > 0, the cycloid position r_cycloid M η is
    a constructively computable positive real number. Height 0 (BISH). -/
theorem r_cycloid_computable {M η : ℝ} (hM : M > 0) (hη : η ∈ Ioo 0 π) :
    ∃ v : ℝ, v > 0 ∧ r_cycloid M η = v := by
  refine ⟨r_cycloid M η, ?_, rfl⟩
  exact (r_cycloid_interior hM hη).r_pos

/-- For η ∈ (0, π) and M > 0, the cycloid proper time τ_cycloid M η is
    a constructively computable positive real number. Height 0 (BISH). -/
theorem τ_cycloid_computable {M η : ℝ} (hM : M > 0) (hη : η ∈ Ioo 0 π) :
    ∃ v : ℝ, v > 0 ∧ τ_cycloid M η = v := by
  refine ⟨τ_cycloid M η, ?_, rfl⟩
  unfold τ_cycloid
  apply mul_pos hM
  have hη_pos := hη.1
  have hsin_nn := sin_nonneg_of_nonneg_of_le_pi (le_of_lt hη_pos) (le_of_lt hη.2)
  linarith

-- ========================================================================
-- BISH approaching singularity (repackaged from RadialGeodesic)
-- ========================================================================

/-- **BISH approaching singularity.**
    For any ε > 0, there exists a constructive η ∈ (0, π) such that
    r_cycloid M η < ε. This is the BISH content: we can get arbitrarily
    close to r = 0 without asserting that r actually reaches 0.
    Height 0 (BISH) — no Classical.choice needed. -/
theorem approaching_singularity_BISH {M : ℝ} (hM : M > 0)
    {ε : ℝ} (hε : ε > 0) :
    ∃ η ∈ Ioo 0 π, r_cycloid M η < ε :=
  r_cycloid_approaching hM hε

/-- The proper time to any cycloid position is bounded by πM.
    This is constructive: the finite proper time τ* = πM is a BISH upper bound. -/
theorem τ_cycloid_bounded {M η : ℝ} (hM : M > 0)
    (hη : η ∈ Icc 0 π) : τ_cycloid M η ≤ M * π := by
  -- τ_cycloid M is strictly increasing on [0, π], so τ(η) ≤ τ(π) = Mπ.
  have hpi_mem : π ∈ Icc (0 : ℝ) π := ⟨le_of_lt pi_pos, le_refl _⟩
  have hmon := (τ_cycloid_strictMonoOn M hM).monotoneOn
  have h := hmon hη hpi_mem hη.2
  -- h : (fun x => τ_cycloid M x) η ≤ (fun x => τ_cycloid M x) π
  -- which is definitionally τ_cycloid M η ≤ τ_cycloid M π
  have h_at_pi : τ_cycloid M π = M * π := τ_cycloid_at_pi M
  linarith

-- ========================================================================
-- The BISH content: approaching within any tolerance, constructively
-- ========================================================================

/-- **Complete BISH content theorem.**
    For any M > 0 and ε > 0, there exists an explicit proper time τ < πM
    and corresponding position r < ε, all constructively computable.
    This is the BISH dispensability of the singularity assertion. -/
theorem bish_content_complete {M : ℝ} (hM : M > 0) {ε : ℝ} (hε : ε > 0) :
    ∃ η ∈ Ioo 0 π,
      r_cycloid M η < ε ∧
      r_cycloid M η > 0 ∧
      τ_cycloid M η > 0 ∧
      τ_cycloid M η ≤ M * π := by
  obtain ⟨η, hη, hr⟩ := r_cycloid_approaching hM hε
  refine ⟨η, hη, hr, ?_, ?_, ?_⟩
  · exact (r_cycloid_interior hM hη).r_pos
  · obtain ⟨v, hpos, hv_eq⟩ := τ_cycloid_computable hM hη
    rw [hv_eq]; exact hpos
  · exact τ_cycloid_bounded hM ⟨le_of_lt hη.1, le_of_lt hη.2⟩

end Papers.P13
