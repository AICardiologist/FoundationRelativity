/-
  CRMLint — Layer 1: Classical Dependency Tracer
  Paper 76 of the Constructive Reverse Mathematics Series

  Traverses Lean 4 Environment to compute the transitive closure of
  constant dependencies for any declaration, then filters to classical
  axioms (Classical.choice, Classical.em, propext, Quot.sound).

  For each classical axiom hit, records the "direct caller" — the last
  non-axiom constant on the dependency path. This is what the pattern
  classifier (Layer 2) uses to determine the CRM pattern.

  Author: Paul C.-K. Lee
  Date: February 2026
-/
import Lean
import CRMLint.Defs

open Lean

namespace CRMLint.Trace

-- ============================================================
-- § 1. Classical Axiom Names
-- ============================================================

/-- The four classical axioms tracked by CRMLint.
    Every theorem over ℝ shows Classical.choice in `#print axioms` —
    this is Mathlib infrastructure. CRMLint distinguishes infrastructure
    from genuine classical content (the entire point of the tool). -/
def classicalAxiomNames : NameSet :=
  NameSet.empty
    |>.insert ``Classical.choice
    |>.insert ``Classical.em
    |>.insert ``propext
    |>.insert ``Quot.sound

def isClassicalAxiom (n : Name) : Bool :=
  classicalAxiomNames.contains n

-- ============================================================
-- § 2. Direct Constant Collection from Expressions
-- ============================================================

/-- Collect all constant names directly referenced in an expression.
    Walks the Expr tree and collects Expr.const nodes. -/
partial def collectExprConsts (e : Expr) (acc : NameSet := {}) : NameSet :=
  match e with
  | .const n _       => acc.insert n
  | .app f a         => collectExprConsts a (collectExprConsts f acc)
  | .lam _ t b _     => collectExprConsts b (collectExprConsts t acc)
  | .forallE _ t b _ => collectExprConsts b (collectExprConsts t acc)
  | .letE _ t v b _  => collectExprConsts b (collectExprConsts v (collectExprConsts t acc))
  | .mdata _ e       => collectExprConsts e acc
  | .proj _ _ e      => collectExprConsts e acc
  | _                => acc

/-- Get all constant names directly referenced by a ConstantInfo
    (from both type and value/proof body). -/
def getDirectDeps (info : ConstantInfo) : NameSet :=
  let fromType := collectExprConsts info.type
  match info.value? with
  | some v => collectExprConsts v fromType
  | none   => fromType

-- ============================================================
-- § 3. Classical Axiom Tracing
-- ============================================================

/-- For a given declaration, find all constants that directly reference
    a classical axiom. Returns pairs of (axiomName, callerName) where
    callerName is the constant whose definition/type directly contains
    a reference to axiomName.

    Uses BFS with a visited set for efficiency. -/
def traceClassicalDeps (env : Environment) (name : Name) :
    Array (Name × Name) := Id.run do
  let mut visited : NameSet := {}
  let mut queue : Array Name := #[name]
  let mut result : Array (Name × Name) := #[]

  while h : queue.size > 0 do
    let current := queue[0]'(by omega)
    queue := queue.extract 1 queue.size

    if visited.contains current then
      continue
    visited := visited.insert current

    match env.find? current with
    | none => pure ()
    | some info =>
      let deps := getDirectDeps info
      for dep in deps.toList do
        if isClassicalAxiom dep then
          result := result.push (dep, current)
        else if !visited.contains dep then
          queue := queue.push dep

  return result

/-- Deduplicate classical entries by (axiomName, callerName) pair. -/
def deduplicateEntries (entries : Array (Name × Name)) : Array (Name × Name) := Id.run do
  let mut seen : NameSet := {}
  let mut result : Array (Name × Name) := #[]
  for (ax, caller) in entries do
    let key := Name.mkStr (Name.mkStr .anonymous (toString ax)) (toString caller)
    if !seen.contains key then
      seen := seen.insert key
      result := result.push (ax, caller)
  return result

-- ============================================================
-- § 4. Summary Statistics
-- ============================================================

/-- Count distinct classical axiom types in a trace result.
    Returns (choice_count, em_count, propext_count, quotSound_count). -/
def countAxiomTypes (entries : Array (Name × Name)) : Nat × Nat × Nat × Nat := Id.run do
  let mut c := 0; let mut e := 0; let mut p := 0; let mut q := 0
  for (ax, _) in entries do
    if ax == ``Classical.choice then c := c + 1
    else if ax == ``Classical.em then e := e + 1
    else if ax == ``propext then p := p + 1
    else if ax == ``Quot.sound then q := q + 1
  return (c, e, p, q)

end CRMLint.Trace
