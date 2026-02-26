/-
  CRMLint — Layer 2: Pattern Classifier (v0.2)
  Paper 76 of the Constructive Reverse Mathematics Series

  Classifies each classical axiom entry point by its CRM pattern.
  Takes the output of Layer 1 (pairs of axiomName × callerName) and
  determines the ClassicalPattern for each.

  v0.2 FIX (critical): Type-aware Decidable classification.
  - Decidable (x = y) for x y : ℕ → BISH (infrastructure)
  - Decidable (x = y) for x y : ℝ → WLPO (essential!)
  - Decidable (∃ n, P n) → LPO (essential!)
  - Quotient.out / Quotient.choice → CLASS (essential!)

  v0.1 BUG: classified Real Decidable instances as infrastructure,
  causing Real.instField to read BISH instead of WLPO.
  The total inverse inv : ℝ → ℝ with inv 0 = 0 requires
  Decidable (x = 0) for x : ℝ, which is WLPO.

  Classification rules (in priority order):
  1. propext → always infrastructure
  2. Quot.sound → always infrastructure
  3. Caller is analytic Decidable (ℝ/ℂ) → WLPO (essential!)
  4. Caller is quotient extraction (Quotient.out/choice) → CLASS
  5. Caller is classical generic (propDecidable/dec/decEq) →
     inspect type: ℝ → WLPO, ∃ → LPO, else → CLASS (conservative)
  6. Caller in BISH infrastructure whitelist → BISH
  7. Caller name contains zorn/Zorn → CLASS
  8. Caller name contains WellOrder → CLASS
  9. Type-based: caller type has Decidable + analytic type → WLPO
  10. Type-based: caller type has Decidable + ∃ → LPO
  11. Classical.em on Σ⁰₁ predicate → MP (conservative)
  12. Default → CLASS (conservative)

  Author: Paul C.-K. Lee
  Date: February 2026
-/
import Lean
import CRMLint.Defs
import CRMLint.Infrastructure

open Lean

namespace CRMLint.Classify

private def hasSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

-- ============================================================
-- § 1. Name-Based Pattern Detection
-- ============================================================

def isZornRelated (name : Name) : Bool :=
  let s := toString name
  hasSubstr s "zorn" || hasSubstr s "Zorn" ||
  hasSubstr s "zorn_preorder" || hasSubstr s "zorn_partialOrder"

def isWellOrderRelated (name : Name) : Bool :=
  let s := toString name
  hasSubstr s "IsWellOrder" || hasSubstr s "WellOrder" ||
  hasSubstr s "wellOrder" || hasSubstr s "isWellOrder" ||
  hasSubstr s "WellFounded.choice"

-- ============================================================
-- § 2. Type-Based Pattern Detection
-- ============================================================

private def realName : Name := `Real
private def complexName : Name := `Complex

/-- Check if an expression references an analytic type (ℝ or ℂ).
    These are the types where Decidable equality costs WLPO. -/
partial def exprReferencesAnalyticType (e : Expr) : Bool :=
  match e with
  | .const n _ => n == realName || n == complexName
  | .app f a => exprReferencesAnalyticType f || exprReferencesAnalyticType a
  | .lam _ t b _ => exprReferencesAnalyticType t || exprReferencesAnalyticType b
  | .forallE _ t b _ => exprReferencesAnalyticType t || exprReferencesAnalyticType b
  | .letE _ t v b _ =>
    exprReferencesAnalyticType t || exprReferencesAnalyticType v || exprReferencesAnalyticType b
  | .mdata _ e => exprReferencesAnalyticType e
  | .proj _ _ e => exprReferencesAnalyticType e
  | _ => false

/-- Check if an expression involves a Decidable instance. -/
partial def exprInvolvesDecidable (e : Expr) : Bool :=
  match e with
  | .const n _ =>
    let s := toString n
    hasSubstr s "Decidable" || hasSubstr s "decidable"
  | .app f a => exprInvolvesDecidable f || exprInvolvesDecidable a
  | .lam _ t b _ => exprInvolvesDecidable t || exprInvolvesDecidable b
  | .forallE _ t b _ => exprInvolvesDecidable t || exprInvolvesDecidable b
  | .letE _ t v b _ =>
    exprInvolvesDecidable t || exprInvolvesDecidable v || exprInvolvesDecidable b
  | .mdata _ e => exprInvolvesDecidable e
  | .proj _ _ e => exprInvolvesDecidable e
  | _ => false

/-- Check if an expression involves an existential quantifier
    over an infinite domain. -/
partial def exprInvolvesExists (e : Expr) : Bool :=
  match e with
  | .const n _ =>
    let s := toString n
    hasSubstr s "Exists" || n == ``Exists
  | .app f a => exprInvolvesExists f || exprInvolvesExists a
  | .lam _ t b _ => exprInvolvesExists t || exprInvolvesExists b
  | .forallE _ t b _ => exprInvolvesExists t || exprInvolvesExists b
  | .letE _ t v b _ =>
    exprInvolvesExists t || exprInvolvesExists v || exprInvolvesExists b
  | .mdata _ e => exprInvolvesExists e
  | .proj _ _ e => exprInvolvesExists e
  | _ => false

/-- Check if a constant's type or value references an analytic type.
    Examines both the type signature and (if available) the proof body. -/
def constReferencesAnalyticType (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some info =>
    exprReferencesAnalyticType info.type ||
    match info.value? with
    | some v => exprReferencesAnalyticType v
    | none   => false
  | none => false

/-- Check if a constant's type or value involves Decidable instances. -/
def constInvolvesDecidable (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some info =>
    exprInvolvesDecidable info.type ||
    match info.value? with
    | some v => exprInvolvesDecidable v
    | none   => false
  | none => false

/-- Check if a constant's type or value involves existential quantifiers. -/
def constInvolvesExists (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some info =>
    exprInvolvesExists info.type ||
    match info.value? with
    | some v => exprInvolvesExists v
    | none   => false
  | none => false

-- ============================================================
-- § 3. Entry Classification
-- ============================================================

/-- Classify a single (axiomName, callerName) pair into a ClassicalPattern.

    This is the core classification engine. Rules are applied in priority
    order. The key v0.2 fix: Decidable instances on ℝ/ℂ are WLPO,
    not infrastructure. Only Decidable on discrete types (ℕ, ℤ, etc.)
    is genuine BISH.

    The `rootName` parameter enables root-context-aware classification:
    when the caller is a generic classical constant (Classical.propDecidable
    has type (p : Prop) → Decidable p — no mention of ℝ), we check
    whether the ROOT declaration involves ℝ as a fallback. This is sound:
    if Real.instField's dependency chain reaches Classical.propDecidable,
    the propDecidable is deciding something about ℝ (WLPO).

    Priority:
    1. Axiom = propext → infrastructure (always)
    2. Axiom = Quot.sound → infrastructure (always)
    3. Caller is analytic Decidable (isAnalyticDecidable) → WLPO
    4. Caller is quotient extraction (Quotient.out/choice) → CLASS
    5. Caller is classical generic (propDecidable/dec/decEq) →
       inspect caller type: ℝ → WLPO, ∃ → LPO,
       else inspect ROOT type: ℝ → WLPO, ∃ → LPO, else CLASS
    6. Caller in BISH infrastructure whitelist → BISH
    7. Caller name ∈ Zorn names → CLASS
    8. Caller name ∈ WellOrder names → CLASS
    9. Type analysis: Decidable + analytic type → WLPO
    10. Type analysis: Decidable + ∃ → LPO
    11. Classical.em + root involves ℝ → WLPO (em for Real decidability)
    12. Classical.em (other) → MP (conservative for Σ⁰₁)
    13. Default → CLASS (conservative) -/
def classifyEntry (env : Environment) (rootName axiomName callerName : Name) :
    ClassicalPattern :=
  -- Rule 1: propext is always infrastructure
  if axiomName == ``propext then
    .propextInfra
  -- Rule 2: Quot.sound is always infrastructure (quotient construction)
  else if axiomName == ``Quot.sound then
    .quotSoundInfra
  -- Rule 3: Caller is an analytic Decidable instance (WLPO, never infra!)
  else if Infrastructure.isAnalyticDecidable callerName then
    .decidableRealEq
  -- Rule 4: Caller is quotient extraction (CLASS, never infra!)
  else if Infrastructure.isQuotientExtraction callerName then
    .wellOrder  -- CLASS via choice extraction
  -- Rule 5: Caller is Classical.propDecidable / Classical.dec / Classical.decEq
  -- The CRM cost depends on WHAT is being decided → inspect the type.
  -- These constants are generic: Classical.propDecidable has type
  -- (p : Prop) → Decidable p with no mention of the decided type.
  -- So we first check caller's type, then fall back to ROOT context.
  else if Infrastructure.isClassicalDecidable callerName then
    -- 5a. Caller's type/value mentions ℝ or ℂ → WLPO
    if constReferencesAnalyticType env callerName then
      .decidableRealEq
    -- 5b. Caller's type/value mentions ∃ → LPO
    else if constInvolvesExists env callerName then
      .decidableExists
    -- 5c. ROOT declaration involves ℝ/ℂ (and is NOT Zorn-related) →
    --     classical content is for Real → WLPO.
    --     Guard: Zorn theorems mention ∃ in their statement (∃ maximal element)
    --     but their propDecidable is for well-ordering, not analytic decidability.
    else if constReferencesAnalyticType env rootName &&
            !isZornRelated rootName then
      .decidableRealEq
    -- 5d. ROOT involves ∃ (and is NOT Zorn-related) → LPO
    else if constInvolvesExists env rootName &&
            !isZornRelated rootName then
      .decidableExists
    -- 5e. Otherwise, conservative: CLASS
    else
      .unclassified
  -- Rule 6: Caller in BISH infrastructure whitelist (discrete types only)
  else if Infrastructure.isInfrastructureName callerName then
    -- Double-check: if caller also references analytic types, override to WLPO
    if constReferencesAnalyticType env callerName &&
       constInvolvesDecidable env callerName then
      .decidableRealEq
    else
      .realInfrastructure  -- genuinely BISH infrastructure
  -- Rule 7: Zorn-related → CLASS
  else if isZornRelated callerName then
    .zorn
  -- Rule 8: Well-ordering → CLASS
  else if isWellOrderRelated callerName then
    .wellOrder
  -- Rule 9: Type-based fallback: Decidable + analytic type → WLPO
  else if constReferencesAnalyticType env callerName &&
          constInvolvesDecidable env callerName then
    .decidableRealEq
  -- Rule 10: Type-based fallback: Decidable + ∃ → LPO
  else if constInvolvesDecidable env callerName &&
          constInvolvesExists env callerName then
    .decidableExists
  -- Rule 11: Classical.em with root-context analysis
  else if axiomName == ``Classical.em then
    -- If the root declaration involves ℝ (and not Zorn), em is for Real → WLPO
    if constReferencesAnalyticType env rootName && !isZornRelated rootName then
      .decidableRealEq
    else
      .emSigma01  -- Conservative MP for Σ⁰₁
  -- Rule 13: Default → CLASS (conservative: unknown pattern)
  else
    .unclassified

/-- Build a ClassicalEntry from a classified (axiomName, callerName) pair. -/
def mkEntry (env : Environment) (rootName axiomName callerName : Name) : ClassicalEntry :=
  let pattern := classifyEntry env rootName axiomName callerName
  let role := if pattern.isInfrastructure then EntryRole.infrastructure else EntryRole.essential
  { axiomName, callerName, pattern, role }

/-- Classify all (axiomName, callerName) pairs from Layer 1 output.
    `rootName` is the declaration being audited — used for context-aware
    classification of generic classical constants. -/
def classifyAll (env : Environment) (rootName : Name)
    (pairs : Array (Name × Name)) : Array ClassicalEntry :=
  pairs.map fun (ax, caller) => mkEntry env rootName ax caller

end CRMLint.Classify
