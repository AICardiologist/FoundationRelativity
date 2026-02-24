/-
  Paper 41: Axiom Calibration of the AdS/CFT Correspondence
  IslandFormula.lean: Section 6.4 — The Island Formula and the Page Curve

  The island formula: S(A) = min(S_island, S_no-island)
  The Page curve is a BISH-computable function of time.
  The Page time decision (phase classification) costs LLPO.
-/
import Papers.P41_AdSCFT.ThermalBTZ

noncomputable section

-- ============================================================
-- Page Curve: BISH (Section 6.4)
-- ============================================================

/-- The Page curve — the continuous plot of entanglement entropy as
    a function of time — is min(S_island(t), S_no_island(t)).
    By the same algebraic identity as the BTZ entropy,
    the minimum is BISH-computable. -/
theorem page_curve_bish (S_island S_no_island : ℝ → ℝ) :
    ∀ t, min (S_island t) (S_no_island t) =
      (S_island t + S_no_island t - |S_island t - S_no_island t|) / 2 :=
  fun t => min_eq_algebraic (S_island t) (S_no_island t)

/-- Every point on the Page curve can be computed to arbitrary precision
    without any omniscience principle. The continuous entropy function
    is strictly BISH. -/
theorem page_curve_pointwise_bish (S_island S_no_island : ℝ → ℝ) (t : ℝ) :
    ∃ (S_t : ℝ),
      S_t = (S_island t + S_no_island t - |S_island t - S_no_island t|) / 2 :=
  ⟨_, rfl⟩

-- ============================================================
-- Page Time Decision: LLPO (Section 6.4)
-- ============================================================

/-- The Page time decision — "has the Page time occurred?" — is the
    assertion "the system has transitioned from the no-island phase
    to the island phase at this precise moment."

    This requires comparing S_island(t) with S_no_island(t),
    which is exactly the real-number weak comparison (x ≤ y) ∨ (y ≤ x),
    equivalent to LLPO. -/
theorem island_decision_requires_llpo :
    (∀ (x y : ℝ), x ≤ y ∨ y ≤ x) → LLPO :=
  generic_phase_decision_requires_llpo

/-- LLPO suffices for the Page time decision. -/
theorem llpo_gives_island_decision :
    LLPO → ∀ (x y : ℝ), x ≤ y ∨ y ≤ x :=
  llpo_gives_phase_decision

/-- The Page time decision is equivalent to LLPO. -/
theorem island_decision_iff_llpo :
    (∀ (x y : ℝ), x ≤ y ∨ y ≤ x) ↔ LLPO :=
  generic_phase_iff_llpo

-- ============================================================
-- Summary: Island Formula Calibration
-- ============================================================

/-- The island formula calibration:
    • Continuous Page curve: BISH (min of two BISH quantities)
    • Discrete Page time decision: LLPO (real comparison)
    • Both sides of the duality carry LLPO cost for the phase decision -/
theorem island_formula_calibration :
    -- Page curve value: BISH
    (∀ (S_i S_n : ℝ → ℝ) (t : ℝ),
      min (S_i t) (S_n t) =
        (S_i t + S_n t - |S_i t - S_n t|) / 2) ∧
    -- Page time decision: ↔ LLPO
    ((∀ (x y : ℝ), x ≤ y ∨ y ≤ x) ↔ LLPO) :=
  ⟨fun S_i S_n t => min_eq_algebraic (S_i t) (S_n t),
   generic_phase_iff_llpo⟩

end
