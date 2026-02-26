/-
  CRMLint — Smoke Tests
  Paper 76 of the Constructive Reverse Mathematics Series

  Calibration tests against known ground truth from the CRM programme.
  Each `#crm_audit` call should produce the expected CRM level.

  Ground truth sources:
  - Pure Nat/Int: BISH (no classical content)
  - ℝ arithmetic: BISH (all Classical.choice is infrastructure)
  - Zorn-dependent: CLASS
  - ℝ decidability: WLPO (if essential, not infrastructure)

  Author: Paul C.-K. Lee
  Date: February 2026
-/
import CRMLint

-- ============================================================
-- § 1. BISH targets (no essential classical content)
-- ============================================================

-- Pure natural number arithmetic: expect BISH
#crm_audit Nat.add_comm
#crm_audit Nat.mul_comm

-- ============================================================
-- § 2. Theorems with classical content
-- ============================================================

-- These will be tested once the tool compiles.
-- Expected calibration targets for Layer 2 refinement:
--
-- #crm_audit Zorn.zorn_partialOrder     -- expect CLASS
-- #crm_audit Real.add_comm              -- expect BISH (infrastructure)
