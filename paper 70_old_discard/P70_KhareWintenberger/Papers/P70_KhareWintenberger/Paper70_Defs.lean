/-
  Paper 70: Serre's Modularity Conjecture is BISH + WLPO
  Paper70_Defs.lean — CRM hierarchy and inherited stage classifications

  This file provides the CRM infrastructure for Paper 70.
  The CRM hierarchy and join operation are identical to Papers 68-69;
  they are duplicated here for self-containment.

  Paper 68 stage classifications and Paper 69 BCDT extensions are
  recorded as definitions (not axioms): these are established results
  from the earlier papers.

  Author: Paul C.-K. Lee
  Date: February 2026
  Zero sorry. Zero warnings target.
-/

import Mathlib.Data.Nat.Basic

-- ============================================================
-- § 1. CRM Hierarchy
-- ============================================================

/-- The constructive reverse mathematics hierarchy.
    BISH ⊂ MP ⊂ LLPO ⊂ WLPO ⊂ LPO ⊂ CLASS. -/
inductive CRMLevel where
  | BISH  : CRMLevel
  | MP    : CRMLevel
  | LLPO  : CRMLevel
  | WLPO  : CRMLevel
  | LPO   : CRMLevel
  | CLASS : CRMLevel
  deriving DecidableEq, Repr

namespace CRMLevel

/-- The join (maximum) of two CRM levels, by exhaustive pattern match.
    Defined so that `simp [join]` or `decide` reduces on concrete constructors. -/
def join : CRMLevel → CRMLevel → CRMLevel
  | BISH,  b      => b
  | a,     BISH   => a
  | CLASS, _      => CLASS
  | _,     CLASS  => CLASS
  | LPO,   _      => LPO
  | _,     LPO    => LPO
  | WLPO,  _      => WLPO
  | _,     WLPO   => WLPO
  | LLPO,  _      => LLPO
  | _,     LLPO   => LLPO
  | MP,    MP     => MP

-- Basic join properties

/-- BISH is strictly below WLPO. -/
theorem bish_ne_wlpo : BISH ≠ WLPO := by decide

/-- Join with BISH is identity (left). -/
theorem join_bish_left (a : CRMLevel) : join BISH a = a := by
  cases a <;> simp [join]

/-- Join with BISH is identity (right). -/
theorem join_bish_right (a : CRMLevel) : join a BISH = a := by
  cases a <;> simp [join]

/-- Join is idempotent. -/
theorem join_self (a : CRMLevel) : join a a = a := by
  cases a <;> simp [join]

end CRMLevel

-- ============================================================
-- § 2. Paper 68 Stage Classifications (Established Results)
-- ============================================================

open CRMLevel

/-- Stage 1 (Langlands-Tunnell): requires WLPO.
    The Arthur-Selberg trace formula involves spectral decomposition
    (eigenvalue isolation: WLPO), orbital integral matching (real
    equality: WLPO), and the converse theorem for GL₃.
    Established in Paper 68, Theorem C. -/
def stage1_class : CRMLevel := CRMLevel.WLPO

/-- Stage 2 (Deformation ring): BISH.
    Schlessinger's criterion, Fontaine-Laffaille theory, finite
    local conditions. Established in Paper 68, Theorem B. -/
def stage2_class : CRMLevel := CRMLevel.BISH

/-- Stage 3 (Hecke algebra): BISH.
    Hecke operators are explicit linear maps; dimension of
    S₂(Γ₀(N)) is computable by Riemann-Roch.
    Established in Paper 68, Theorem B. -/
def stage3_class : CRMLevel := CRMLevel.BISH

/-- Stage 4 (Numerical criterion / CM base case): BISH.
    Subsumed by Stage 5 in the published proof; CM base case
    (Rubin's Euler system) uses effective Chebotarev.
    Established in Paper 68, Theorem B. -/
def stage4_class : CRMLevel := CRMLevel.BISH

/-- Stage 5 (Taylor-Wiles patching): BISH.
    Brochard (2017) eliminates the Fan Theorem; effective Chebotarev
    eliminates Markov's Principle.
    Established in Paper 68, Theorem A. -/
def stage5_class : CRMLevel := CRMLevel.BISH

-- ============================================================
-- § 3. Paper 69 BCDT Extensions (Established Results)
-- ============================================================

/-- Breuil's classification of finite flat group schemes: BISH.
    Strongly divisible lattices in filtered φ-modules.
    Established in Paper 69, §4. -/
def breuil_class : CRMLevel := CRMLevel.BISH

/-- The Diamond-Taylor 3-5 switching argument: BISH.
    Bounded polynomial evaluation search.
    Established in Paper 69, §3. -/
def switch35_class : CRMLevel := CRMLevel.BISH

/-- Conrad's local-global compatibility: BISH.
    Explicit finite-dimensional representation comparisons.
    Established in Paper 69, §4. -/
def conrad_class : CRMLevel := CRMLevel.BISH

-- ============================================================
-- § 4. Reference Results from Papers 68-69
-- ============================================================

/-- Paper 68: Wiles's proof is BISH + WLPO. -/
theorem paper68_classification :
    join stage1_class (join stage2_class (join stage3_class
      (join stage4_class stage5_class))) = CRMLevel.WLPO := by
  simp [stage1_class, stage2_class, stage3_class,
        stage4_class, stage5_class, join]

/-- Paper 68: Stages 2-5 are BISH. -/
theorem paper68_engine_is_bish :
    join stage2_class (join stage3_class
      (join stage4_class stage5_class)) = CRMLevel.BISH := by
  simp [stage2_class, stage3_class, stage4_class, stage5_class, join]

/-- Paper 69: BCDT is BISH + WLPO. -/
theorem paper69_classification :
    join stage1_class
      (join stage2_class
        (join stage3_class
          (join stage4_class
            (join stage5_class
              (join breuil_class
                (join switch35_class conrad_class)))))) = CRMLevel.WLPO := by
  simp [stage1_class, stage2_class, stage3_class,
        stage4_class, stage5_class, breuil_class,
        switch35_class, conrad_class, join]
