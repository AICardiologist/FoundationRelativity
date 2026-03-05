/-
  CRMLint — Namespace Scan Tests
  Paper 76 of the Constructive Reverse Mathematics Series

  Batch scans of Mathlib namespaces for the proof technique atlas.

  Author: Paul C.-K. Lee
  Date: February 2026
-/
import CRMLint
import Mathlib.Order.Zorn
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Int.Basic

-- ============================================================
-- § 1. Small namespace test
-- ============================================================

#crm_scan Nat

-- ============================================================
-- § 2. Zorn-adjacent (expect heavy CLASS)
-- ============================================================

#crm_scan Zorn
