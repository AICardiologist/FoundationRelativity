/-
Papers/P8_LPO_IsingBound/PartB_Main.lean
Assembly of the LPO ↔ BMC equivalence (Theorem 5.1, Part B).

Main result:
  LPO ↔ BMC (Bounded Monotone Convergence)

Forward: [Bridges–Vîță 2006] (axiomatized as bmc_of_lpo).
Backward: By encoding binary sequences into free energy sequences
  of the 1D Ising model and extracting decisions from convergence.

Combined with Part A:
  - Part A: the empirical content (finite-size bounds) is BISH
  - Part B: the idealization (limit existence) costs exactly LPO
  - Together: LPO is genuine but dispensable for predictions

Axiom profile:
  lpo_of_bmc:  [propext, Classical.choice, Quot.sound]  (no custom axioms)
  lpo_iff_bmc: [propext, Classical.choice, Quot.sound, bmc_of_lpo]  (one cited axiom)
-/
import Papers.P8_LPO_IsingBound.PartB_Forward
import Papers.P8_LPO_IsingBound.PartB_Backward

namespace Papers.P8

-- ========================================================================
-- The Equivalence Theorem
-- ========================================================================

/-- **LPO ↔ BMC (Theorem 5.1, Part B).**

    Over BISH, the Limited Principle of Omniscience is equivalent to
    Bounded Monotone Convergence.

    Forward (bmc_of_lpo): [Bridges–Vîță 2006, Theorem 2.1.5]. Axiomatized.
    Backward (lpo_of_bmc): By encoding binary sequences into 1D Ising
    free energy sequences and extracting decisions from convergence behavior.

    Combined with Part A (ising_1d_dispensability), this establishes that
    the LPO cost of the thermodynamic limit is genuine (it is equivalent to,
    not merely sufficient for, a known omniscience principle) and dispensable
    (the finite-system predictions with error bounds require no omniscience). -/
theorem lpo_iff_bmc : LPO ↔ BMC :=
  ⟨bmc_of_lpo, lpo_of_bmc⟩

-- ========================================================================
-- Axiom audit
-- ========================================================================

-- The backward direction should have NO custom axioms:
#print axioms lpo_of_bmc
-- Expected: [propext, Classical.choice, Quot.sound]

-- The full equivalence depends on the axiomatized forward direction:
#print axioms lpo_iff_bmc
-- Expected: [propext, Classical.choice, Quot.sound, Papers.P8.bmc_of_lpo]

end Papers.P8
