/-
  Paper 44: The Measurement Problem Dissolved
  Main/Synthesis.lean — Main theorem collecting all three calibrations

  The measurement problem is not one problem but three, each requiring
  a distinct constructive principle:

  | Interpretation    | Physical assertion              | Principle |
  |-------------------|---------------------------------|-----------|
  | Copenhagen        | Superposition decidability      | WLPO      |
  | Many-Worlds       | Complete branching trees        | DC        |
  | Bohmian Mechanics | Asymptotic velocity existence   | LPO       |

  Logical relationships:
  - WLPO < LPO (strict: LPO → WLPO but not conversely)
  - DC ∦ LPO (incomparable: neither implies the other in BISH)
  - DC ∦ WLPO (incomparable)
  No interpretation is constructively free. The three sit at genuinely
  different positions in the constructive hierarchy.
-/
import Papers.P44_MeasurementDissolved.Copenhagen.Copenhagen
import Papers.P44_MeasurementDissolved.ManyWorlds.ManyWorlds
import Papers.P44_MeasurementDissolved.Bohmian.BohmianLPO

namespace Papers.P44

-- ========================================================================
-- The Measurement Problem Dissolved
-- ========================================================================

/-- **Main Theorem.** The measurement problem is dissolved: the three major
    quantum mechanics interpretations require logically distinct constructive
    principles.

    - Copenhagen (superposition decidability) ↔ WLPO
    - Many-Worlds (complete branching trees) ↔ DC (Dependent Choice)
    - Bohmian Mechanics (asymptotic velocity existence) ↔ LPO

    Since WLPO, LPO, and DC are provably distinct principles in BISH
    (WLPO < LPO strictly, DC incomparable with both), the three interpretations
    are not "different ways of saying the same thing" — they have genuinely
    different logical costs. The measurement problem may have been a category error. -/
theorem measurement_problem_dissolved :
    (CopenhagenPostulate ↔ WLPO) ∧
    (ManyWorldsPostulate ↔ DC) ∧
    (BohmianAsymptoticVelocity ↔ LPO) :=
  ⟨copenhagen_iff_WLPO, manyworlds_iff_DC, bohmian_iff_LPO⟩

-- ========================================================================
-- Corollary: Bohmian is strictly stronger than Copenhagen
-- ========================================================================

/-- Bohmian mechanics implies Copenhagen: if trajectories have asymptotic
    velocities (LPO), then superposition is decidable (WLPO). -/
theorem bohmian_implies_copenhagen :
    BohmianAsymptoticVelocity → CopenhagenPostulate :=
  fun h => copenhagen_iff_WLPO.mpr (lpo_implies_wlpo (bohmian_iff_LPO.mp h))

/-- The interpretation hierarchy at the level of constructive principles. -/
theorem interpretation_hierarchy :
    (LPO → WLPO) ∧
    (BohmianAsymptoticVelocity → CopenhagenPostulate) :=
  ⟨lpo_implies_wlpo, bohmian_implies_copenhagen⟩

-- ========================================================================
-- Strong Copenhagen analysis (added in revision)
-- ========================================================================

/-- **Theorem 3.2.** The strong Copenhagen postulate (α = 0 ∨ α ≠ 0,
    without double-negation weakening) implies LPO.

    This is the referee-requested comparison: if one formalizes Copenhagen
    with full decidability rather than WLPO-strength weak decidability,
    the calibration shifts from WLPO to LPO. This validates WLPO as the
    *minimal* constructive content of the measurement postulate. -/
theorem strong_copenhagen_calibrates_at_LPO :
    CopenhagenStrong → LPO :=
  strong_copenhagen_implies_LPO

/-- The strong postulate strictly subsumes the weak postulate. -/
theorem strong_subsumes_weak :
    CopenhagenStrong → CopenhagenPostulate :=
  strong_implies_weak

/-- The formalization spectrum: strengthening the Copenhagen postulate
    shifts the calibration from WLPO to LPO.
    - Weak (α = 0 ∨ ¬¬(α ≠ 0)): WLPO-strength
    - Strong (α = 0 ∨ α ≠ 0): LPO-strength
    This quantifies the constructive cost of the double-negation weakening. -/
theorem copenhagen_spectrum :
    (CopenhagenPostulate → WLPO) ∧
    (CopenhagenStrong → LPO) ∧
    (CopenhagenStrong → CopenhagenPostulate) :=
  ⟨copenhagen_implies_WLPO, strong_copenhagen_implies_LPO, strong_implies_weak⟩

end Papers.P44
