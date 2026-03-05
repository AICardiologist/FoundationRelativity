/-
  CRMLint — Mathlib Calibration Tests (v0.2)
  Paper 76 of the Constructive Reverse Mathematics Series

  Tests against Mathlib theorems with known CRM ground truth.

  v0.2 CHANGE: Real.instField must now read WLPO, not BISH.
  The total inverse inv : ℝ → ℝ (with inv 0 = 0) requires
  Decidable (x = 0) for x : ℝ, which is WLPO.
  (Bridges & Richman 1987, Ch 1.)

  Expected calibration:
    Nat.add_comm  → BISH (0 classical)
    Int.add_comm  → BISH (infra only: propext/Quot.sound for ℤ quotient)
    add_comm      → BISH (type-polymorphic, no ℝ content)
    zorn_le       → CLASS (essential: Classical.indefiniteDescription)
    Real.instField → WLPO (essential: Decidable(ℝ eq) for total inverse)

  Author: Paul C.-K. Lee
  Date: February 2026
-/
import CRMLint
import Mathlib.Order.Zorn
import Mathlib.Data.Real.Basic

-- ============================================================
-- § 1. BISH targets (pure arithmetic)
-- ============================================================

-- Pure Nat: zero classical content → BISH
#crm_audit Nat.add_comm
-- Pure Int: infrastructure only (propext/Quot.sound for ℤ quotient) → BISH
#crm_audit Int.add_comm

-- ============================================================
-- § 2. Known CLASS targets (Zorn)
-- ============================================================

-- Zorn's lemma: ground truth CLASS
#crm_audit zorn_le

-- ============================================================
-- § 3. ℝ theorems (the critical v0.2 fix)
-- ============================================================

-- Generic add_comm (type-polymorphic, not ℝ-specific) → BISH
#crm_audit add_comm

-- Real.instField: MUST read WLPO (not BISH!)
-- The total inverse inv : ℝ → ℝ with inv 0 = 0
-- requires Decidable (x = 0) for x : ℝ → WLPO
#crm_audit Real.instField

-- ============================================================
-- § 4. Compact output for batch comparison
-- ============================================================

#crm_audit_compact Nat.add_comm
#crm_audit_compact Int.add_comm
#crm_audit_compact zorn_le
#crm_audit_compact add_comm
#crm_audit_compact Real.instField
