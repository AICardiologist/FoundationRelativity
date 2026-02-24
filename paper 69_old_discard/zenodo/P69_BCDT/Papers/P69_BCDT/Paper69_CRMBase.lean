/-
  Paper 69: The Modularity Theorem is BISH + WLPO
  Paper69_CRMBase.lean — CRM hierarchy and stage classifications

  This file provides the shared CRM infrastructure for Paper 69.
  The CRM hierarchy and join operation are identical to Paper 68;
  they are duplicated here for self-containment.

  Stage classifications from Paper 68 are recorded as definitions
  (not axioms): the classifications are justified in Paper 68 and
  taken as established results here.

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
-- § 3. Paper 68 Main Result (Reference)
-- ============================================================

/-- Paper 68 classification: Wiles's proof is BISH + WLPO. -/
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
