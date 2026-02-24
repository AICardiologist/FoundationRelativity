/-
  Paper 24: LLPO Equivalence via Kochen-Specker Contextuality
  Main/AxiomAudit.lean — Comprehensive axiom audit

  ONE custom axiom: llpo_real_of_llpo (LLPO → real sign decision).
  This is the same axiom as Paper 21, establishing the standard
  equivalence between binary-sequence LLPO and real-valued LLPO.

  The only other non-standard axiom is Lean.ofReduceBool from
  native_decide, which is a kernel axiom (not a custom axiom).
-/
import Papers.P24_KochenSpecker.Main.Stratification

namespace Papers.P24

-- ========================================================================
-- Part A: BISH (no custom axioms, only Lean.ofReduceBool from native_decide)
-- ========================================================================
section PartA_Audit

#print axioms cega_uncolorable
-- Expected: [Lean.ofReduceBool]

#print axioms finite_context_witness
-- Expected: [propext, Classical.choice, Quot.sound]

#print axioms ks_failing_context
-- Expected: [propext, Classical.choice, Quot.sound, Lean.ofReduceBool]

#print axioms partA_summary
-- Expected: [propext, Classical.choice, Quot.sound, Lean.ofReduceBool]

end PartA_Audit

-- ========================================================================
-- Part B: LLPO calibration (1 custom axiom: llpo_real_of_llpo)
-- ========================================================================
section PartB_Audit

#print axioms ksAsymmetry_nonpos_implies_even_false
-- Expected: [propext, Classical.choice, Quot.sound]

#print axioms ksAsymmetry_nonneg_implies_odd_false
-- Expected: [propext, Classical.choice, Quot.sound]

#print axioms ks_sign_of_llpo
-- Expected: [propext, Classical.choice, Quot.sound, llpo_real_of_llpo]

#print axioms llpo_of_ks_sign
-- Expected: [propext, Classical.choice, Quot.sound]

#print axioms llpo_iff_ks_sign
-- Expected: [propext, Classical.choice, Quot.sound, llpo_real_of_llpo]

end PartB_Audit

-- ========================================================================
-- Hierarchy (no custom axioms)
-- ========================================================================
section Hierarchy_Audit

#print axioms lpo_implies_wlpo
-- Expected: [propext]

#print axioms wlpo_implies_llpo
-- Expected: [propext, Quot.sound]

end Hierarchy_Audit

-- ========================================================================
-- Main result
-- ========================================================================
section Main_Audit

#print axioms ks_stratification
-- Expected: [propext, Classical.choice, Quot.sound,
--            Lean.ofReduceBool, llpo_real_of_llpo]

end Main_Audit

/-
  SUMMARY: One custom axiom across all theorems: llpo_real_of_llpo.

  This is the standard constructive equivalence:
    LLPO (binary sequences) → (∀ x : ℝ, x ≤ 0 ∨ 0 ≤ x)
  established by Ishihara (2006) and Bridges-Richman (1987).

  The Lean.ofReduceBool axiom from native_decide is a kernel axiom,
  not a custom mathematical axiom. It certifies that the compiled
  code agrees with the kernel evaluator.

  The axiom profile exactly matches Paper 21 (Bell nonlocality),
  confirming the structural identity of Bell and KS logical costs.
-/

end Papers.P24
