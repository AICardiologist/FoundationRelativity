/-
  CRMLint — Report Formatting
  Paper 76 of the Constructive Reverse Mathematics Series

  Pretty-print CRM audit results for the `#crm_audit` command.

  Author: Paul C.-K. Lee
  Date: February 2026
-/
import Lean
import CRMLint.Defs

open Lean

namespace CRMLint.Report

/-- Format a single ClassicalEntry as a human-readable string. -/
def formatEntry (e : ClassicalEntry) : String :=
  let roleStr := toString e.role
  let patStr := toString e.pattern
  s!"  [{roleStr}] {e.callerName} via {e.axiomName} — {patStr}"

/-- Format a full CRMAuditResult as a multi-line string. -/
def formatResult (r : CRMAuditResult) : String := Id.run do
  let mut lines : Array String := #[]
  lines := lines.push s!"CRM Audit: {r.declName}"
  lines := lines.push s!"  Level: {r.level}"
  lines := lines.push s!"  Classical entries: {r.totalClassicalDeps} total \
    ({r.infrastructureCount} infrastructure, {r.essentialCount} essential)"

  -- Show essential entries first
  let essentials := r.entries.filter (·.role == .essential)
  if essentials.size > 0 then
    lines := lines.push ""
    lines := lines.push s!"  Essential classical content ({essentials.size}):"
    for e in essentials do
      lines := lines.push (formatEntry e)

  -- Show infrastructure summary (count only, not individual entries)
  let infras := r.entries.filter (·.role == .infrastructure)
  if infras.size > 0 then
    lines := lines.push ""
    lines := lines.push s!"  Infrastructure ({infras.size} entries, suppressed)"

  return "\n".intercalate lines.toList

/-- Compact one-line summary for batch output. -/
def formatCompact (r : CRMAuditResult) : String :=
  s!"{r.declName}: {r.level} ({r.essentialCount} essential, \
    {r.infrastructureCount} infra)"

/-- Format a namespace scan summary as a multi-line report. -/
def formatNamespaceSummary (s : NamespaceSummary) : String := Id.run do
  let mut lines : Array String := #[]
  lines := lines.push s!"CRM Namespace Scan: {s.namespace_}"
  lines := lines.push s!"  Total declarations scanned: {s.totalDecls}"
  lines := lines.push ""
  lines := lines.push "  Level distribution:"
  lines := lines.push s!"    BISH:     {s.bishCount}"
  lines := lines.push s!"    BISH+MP:  {s.bishMPCount}"
  lines := lines.push s!"    LLPO:     {s.llpoCount}"
  lines := lines.push s!"    WLPO:     {s.wlpoCount}"
  lines := lines.push s!"    LPO:      {s.lpoCount}"
  lines := lines.push s!"    CLASS:    {s.classCount}"

  if s.hotspots.size > 0 then
    lines := lines.push ""
    lines := lines.push s!"  Hotspots (top {s.hotspots.size} by essential classical content):"
    for (name, level, ess) in s.hotspots do
      lines := lines.push s!"    {name}: {level} ({ess} essential)"

  return "\n".intercalate lines.toList

end CRMLint.Report
