/-
  CRMLint — #crm_audit Command
  Paper 76 of the Constructive Reverse Mathematics Series

  The user-facing command that composes Layers 1–3:
    Layer 1 (Trace): transitive classical dependency tracing
    Layer 2 (Classify): pattern classification
    Layer 3 (here): concentration analysis and level computation

  Usage:
    #crm_audit Nat.add_comm
    #crm_audit Real.tendsto_sum_of_hasSum

  Output:
    CRM Audit: Nat.add_comm
      Level: BISH
      Classical entries: 0 total (0 infrastructure, 0 essential)

  Author: Paul C.-K. Lee
  Date: February 2026
-/
import Lean
import CRMLint.Defs
import CRMLint.Trace
import CRMLint.Classify
import CRMLint.Report

open Lean Elab Command

namespace CRMLint.Audit

-- ============================================================
-- § 1. Core Audit Function
-- ============================================================

/-- Perform a full CRM audit on a declaration.
    Composes Layer 1 (trace), Layer 2 (classify), and Layer 3 (analyze).
    Returns a structured CRMAuditResult. -/
def crmAudit (env : Environment) (name : Name) : CRMAuditResult :=
  -- Layer 1: trace classical dependencies
  let rawDeps := Trace.traceClassicalDeps env name
  let deps := Trace.deduplicateEntries rawDeps

  -- Layer 2: classify each entry (pass rootName for context-aware classification
  -- of generic classical constants like Classical.propDecidable)
  let entries := Classify.classifyAll env name deps

  -- Layer 3: concentration analysis
  let infraCount := entries.filter (·.role == .infrastructure) |>.size
  let essentialCount := entries.filter (·.role == .essential) |>.size
  let essentialEntries := entries.filter (·.role == .essential)

  -- Compute CRM level as join of all essential entries' pattern levels.
  -- This mirrors the manual audit pattern: stage costs joined (P68 asymmetry theorem).
  -- Infrastructure entries contribute BISH (= identity for join).
  let level := essentialEntries.foldl
    (fun acc e => CRMLevel.join acc e.pattern.toCRMLevel)
    CRMLevel.BISH

  { declName := name
    totalClassicalDeps := entries.size
    entries
    infrastructureCount := infraCount
    essentialCount := essentialCount
    level }

-- ============================================================
-- § 2. #crm_audit Command
-- ============================================================

/-- The `#crm_audit` command. Performs a full CRM audit on a declaration
    and prints the result.

    Usage: `#crm_audit myTheoremName` -/
elab "#crm_audit " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let result := crmAudit env name
  logInfo m!"{Report.formatResult result}"

/-- Compact version for batch use. -/
elab "#crm_audit_compact " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let result := crmAudit env name
  logInfo m!"{Report.formatCompact result}"

-- ============================================================
-- § 3. Namespace Batch Scanner
-- ============================================================

/-- Collect all theorem/definition names in the environment matching a prefix. -/
def collectNamespaceDecls (env : Environment) (prefix_ : Name) : Array Name := Id.run do
  let mut result : Array Name := #[]
  for (name, info) in env.constants.map₁.toList do
    if prefix_.isPrefixOf name then
      match info with
      | .thmInfo _  => result := result.push name
      | .defnInfo _ => result := result.push name
      | _ => pure ()
  return result

/-- Scan an entire namespace and produce a summary.
    `maxDecls` limits the number of declarations scanned (0 = no limit). -/
def scanNamespace (env : Environment) (prefix_ : Name)
    (maxDecls : Nat := 0) (hotspotCount : Nat := 10) : NamespaceSummary := Id.run do
  let allDecls := collectNamespaceDecls env prefix_
  let decls := if maxDecls > 0 && allDecls.size > maxDecls
    then allDecls.extract 0 maxDecls
    else allDecls

  let mut bish := 0; let mut bishMP := 0; let mut llpo := 0
  let mut wlpo := 0; let mut lpo := 0; let mut cls := 0
  let mut hotspots : Array (Name × CRMLevel × Nat) := #[]

  for name in decls do
    let result := crmAudit env name
    match result.level with
    | .BISH    => bish := bish + 1
    | .BISH_MP => bishMP := bishMP + 1
    | .LLPO    => llpo := llpo + 1
    | .WLPO    => wlpo := wlpo + 1
    | .LPO     => lpo := lpo + 1
    | .CLASS   => cls := cls + 1
    -- Track hotspots (declarations with most essential classical content)
    if result.essentialCount > 0 then
      hotspots := hotspots.push (name, result.level, result.essentialCount)

  -- Sort hotspots by essential count descending, take top N
  let sortedHotspots := hotspots.qsort (fun a b => a.2.2 > b.2.2)
  let topHotspots := sortedHotspots.extract 0 (min hotspotCount sortedHotspots.size)

  { namespace_ := prefix_
    totalDecls := decls.size
    bishCount := bish
    bishMPCount := bishMP
    llpoCount := llpo
    wlpoCount := wlpo
    lpoCount := lpo
    classCount := cls
    hotspots := topHotspots }

/-- The `#crm_scan` command. Scans all theorems/definitions in a namespace.

    Usage: `#crm_scan Mathlib.NumberTheory`
    Scans up to 500 declarations by default. -/
elab "#crm_scan " id:ident : command => do
  let prefix_ := id.getId
  let env ← getEnv
  let summary := scanNamespace env prefix_ (maxDecls := 500)
  logInfo m!"{Report.formatNamespaceSummary summary}"

/-- Scan with configurable limit.
    Usage: `#crm_scan_all Mathlib.NumberTheory` (no limit) -/
elab "#crm_scan_all " id:ident : command => do
  let prefix_ := id.getId
  let env ← getEnv
  let summary := scanNamespace env prefix_ (maxDecls := 0)
  logInfo m!"{Report.formatNamespaceSummary summary}"

end CRMLint.Audit
