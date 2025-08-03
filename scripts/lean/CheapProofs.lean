/-
  CheapProofs.lean
  
  Runs in CI: `lake exe cheap_proofs`
  Flags any declaration that:
    • is a theorem/lemma
    • has no sorry
    • AND whose reduced proof term mentions only
      Init.*, Std.*, Tactic.*, Classical.*, Logic.*, Unit, True, False, PUnit
      
  This prevents the use of Unit/() tricks to fake "0 sorries" status.
-/

import Lean

open Lean Elab Meta

/-- Check if a constant name is "harmless" (i.e., doesn't contain real mathematical content) -/
def isHarmless (n : Name) : Bool :=
  n.isInternal || n.isAnonymous ||
  n.getPrefix.isPrefixOf `Init ||
  n.getPrefix.isPrefixOf `Std ||
  n.getPrefix.isPrefixOf `Tactic ||
  n.getPrefix.isPrefixOf `Classical ||
  n.getPrefix.isPrefixOf `Logic ||
  n == ``Unit || n == ``True || n == ``False || n == ``PUnit ||
  n == ``Eq || n == ``HEq || n == ``rfl || n == ``trivial ||
  n == ``And.intro || n == ``Iff.intro || n == ``Exists.intro

/-- Get all constants used in an expression -/
partial def getUsedConstNames (e : Expr) : MetaM (Array Name) := do
  let mut result := #[]
  let rec visit (e : Expr) : MetaM Unit := do
    match e with
    | .const name _ => result := result.push name
    | .app fn arg => do
        visit fn
        visit arg
    | .lam _ _ body _ => visit body
    | .forallE _ _ body _ => visit body
    | .letE _ _ value body _ => do
        visit value
        visit body
    | .proj _ _ e => visit e
    | .mdata _ e => visit e
    | _ => pure ()
  visit e
  return result

/-- Check if a proof only uses "cheap" constants -/
def proofIsCheap (env : Environment) (decl : Name) : MetaM Bool := do
  let some info := env.find? decl | return false
  let some val := info.value? | return false
  let used ← getUsedConstNames val
  return used.all isHarmless

/-- Check if a declaration has a comment indicating it's allowed to be short -/
def hasAllowShortProofComment (env : Environment) (decl : Name) : Bool :=
  -- For now, we don't implement comment checking
  -- This would require parsing source locations
  false

/-- Main entry point -/
def main : IO Unit := do
  let searchPath ← initSearchPath none
  let env ← importModules [{ module := `FoundationRelativity }] {}
  
  let mut cheapProofs : Array (Name × String) := #[]
  
  -- Check all declarations
  for (name, info) in env.constants do
    if info.isTheorem && !name.isInternal then
      -- Skip if it has sorry
      if !info.value?.any (·.hasSorry) then
        -- Check if it's cheap
        let ctx : Core.Context := { fileName := "", fileMap := default }
        let state : Core.State := {}
        let isCheap ← Core.CoreM.toIO 
          (MetaM.run' (ctx := {}) (s := {}) do proofIsCheap env name) 
          ctx state
        match isCheap with
        | .ok (true, _) =>
          if !hasAllowShortProofComment env name then
            let module := name.getPrefix
            cheapProofs := cheapProofs.push (name, s!"{module}")
        | _ => pure ()
  
  if cheapProofs.size > 0 then
    IO.eprintln "⚠️  Cheap proofs found:"
    IO.eprintln ""
    for (name, module) in cheapProofs do
      IO.eprintln s!"  ❌ {name} in {module}"
    IO.eprintln ""
    IO.eprintln s!"Total: {cheapProofs.size} cheap proofs"
    IO.eprintln "Replace them with either `sorry` or a substantive proof."
    IO.Process.exit 1
  else
    IO.println "✅ No cheap proofs found"