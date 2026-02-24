/-
  Paper 24: LLPO Equivalence via Kochen-Specker Contextuality
  Main/Stratification.lean — The KS stratification theorem

  Kochen-Specker contextuality exhibits observable-dependent logical cost:
    Level 1 (BISH): KS uncolorability is a finite combinatorial fact
    Level 2 (LLPO): The KS sign decision ↔ LLPO
    Level 3 (Hierarchy): WLPO → LLPO (strict hierarchy)

  This mirrors Paper 21's Bell stratification — confirming that
  Bell nonlocality and KS contextuality have identical logical cost.
-/
import Papers.P24_KochenSpecker.PartA.PartA_Main
import Papers.P24_KochenSpecker.PartB.PartB_Main

namespace Papers.P24

/-- The KS stratification theorem:
    1. (BISH) The CEGA graph is KS-uncolorable
    2. (LLPO) The KS sign decision is equivalent to LLPO
    3. (Hierarchy) WLPO → LLPO (strict hierarchy) -/
theorem ks_stratification :
    -- Level 1: BISH (KS uncolorability)
    isKSUncolorable cegaGraph ∧
    -- Level 2: LLPO equivalence
    (LLPO ↔ KSSignDecision) ∧
    -- Level 3: Hierarchy (WLPO → LLPO)
    (WLPO → LLPO) :=
  ⟨cega_uncolorable, llpo_iff_ks_sign, wlpo_implies_llpo⟩

-- ============================================================
-- Axiom audit
-- Expected: [propext, Classical.choice, Quot.sound,
--            Lean.ofReduceBool, llpo_real_of_llpo]
-- ============================================================
#print axioms ks_stratification

end Papers.P24
