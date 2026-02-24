/-
Papers/P15_Noether/Main.lean
Paper 15: Noether's Theorem and the Logical Cost of Global Conservation Laws.

Assembly module: imports all components and runs axiom audits.

Results summary:

PART A (BISH content — Level 0):
  • noether_conservation: Σ_i [dE/dt terms] = 0 (energy conservation)
  • energyDensity_nonneg: 0 ≤ ε_i when V ≥ 0
  • totalEnergy_nonneg: 0 ≤ E when V ≥ 0
  • partialEnergy_mono: E_N is monotone increasing when V ≥ 0
  • sum_shift: Σ_i f(next(i)) = Σ_i f(i) (periodic BC invariance)

  Axiom profile: propext, Quot.sound (standard Mathlib infrastructure).
  No omniscience principles. Pure BISH.

PART B (LPO equivalence — Level 1):
  • global_energy_iff_LPO: global energy existence ↔ LPO
  • npsc_iff_bmc: NPSC ↔ BMC (abstract framework)
  • npsc_iff_lpo: NPSC ↔ LPO

  Axiom profile: adds bmc_of_lpo, lpo_of_bmc (axiomatized, cited from
  Bridges–Vîță 2006 and Paper 8 respectively).

Four physical domains, one logical structure (BMC ↔ LPO):
  | Domain             | Bounded Monotone Sequence | LPO Content          |
  |---------------------|---------------------------|----------------------|
  | Stat. Mech. (P8)    | Free energy f_N          | f_∞ exists exactly   |
  | Gen. Rel. (P13)     | Radial coordinate r(τ)   | r → 0 exactly        |
  | Quantum Meas. (P14) | Coherence c(N)           | c → 0 (collapse)     |
  | Conservation (P15)  | Partial energy E_N       | E = lim E_N exists   |
-/
import Papers.P15_Noether.GlobalEnergy
import Papers.P15_Noether.LocalConservation

namespace Papers.P15

-- ========================================================================
-- Part A: BISH content (axiom audit)
-- ========================================================================

section BISH

-- Noether's theorem (energy conservation)
#check @noether_conservation
#check @totalEnergyRate

-- Energy density properties
#check @energyDensity_nonneg
#check @totalEnergy_nonneg
#check @kineticDensity_nonneg
#check @gradientDensity_nonneg

-- Partial energy properties
#check @partialEnergy_mono
#check @partialEnergy_nonneg
#check @partialEnergy_succ
#check @partialEnergy_zero
#check @infiniteEnergyDensity_nonneg

-- Shift invariance (periodic BC)
#check @sum_shift
#check @sum_shift_prev
#check @fin_next_bijective
#check @fin_prev_bijective

-- Axiom certificates: should show only propext, Quot.sound
-- (standard Mathlib infrastructure; no omniscience principles)
#print axioms noether_conservation
#print axioms energyDensity_nonneg
#print axioms totalEnergy_nonneg
#print axioms partialEnergy_mono
#print axioms partialEnergy_nonneg
#print axioms sum_shift

end BISH

-- ========================================================================
-- Part B: LPO equivalence (axiom audit)
-- ========================================================================

section LPO_Equivalence

#check @global_energy_iff_LPO
#check @npsc_iff_bmc
#check @npsc_iff_lpo
#check @partialEnergy_is_nonneg_partial_sum

-- Axiom certificates: should show bmc_of_lpo, lpo_of_bmc in addition
-- to standard Mathlib axioms
#print axioms global_energy_iff_LPO
#print axioms npsc_iff_bmc
#print axioms npsc_iff_lpo

end LPO_Equivalence

end Papers.P15
