/-
  CRMLint — Infrastructure Whitelist
  Paper 76 of the Constructive Reverse Mathematics Series

  Identifies classical axiom dependencies that are Lean 4 / Mathlib
  infrastructure artifacts rather than genuine mathematical classical content.

  CRITICAL DISTINCTION (v0.2 fix):
  - Decidable (x = y) for x y : ℕ → genuinely BISH (bounded computation)
  - Decidable (x = y) for x y : ℝ → genuinely WLPO (Cauchy equality undecidable)
  - propext, Quot.sound → always infrastructure (no CRM content)
  - Quot.mk, Quot.lift, Quot.ind → quotient CONSTRUCTION (BISH)
  - Quotient.out, Quotient.choice → quotient EXTRACTION (CLASS, never whitelist)

  v0.1 BUG: blanket-classified Classical.propDecidable, Classical.dec,
  and Real Decidable instances as infrastructure. This erased the WLPO
  cost of Real.instField (total inv requires Decidable (x = 0) for x : ℝ).
  Real.instField genuinely costs WLPO, not BISH.

  v0.2 FIX: Infrastructure whitelist now restricted to:
  (a) Decidable instances on discrete types (ℕ, ℤ, ℚ, Fin, Bool)
  (b) Quotient construction (Quot.mk/lift/ind, NOT Quot.out)
  (c) propext, Quot.sound (proof-irrelevance, no CRM content)
  (d) Lean kernel artifacts (Lean.Grind, trustCompiler)

  Everything else — including Classical.propDecidable, Classical.dec,
  Classical.decEq, Real Decidable instances — is NOT whitelisted.
  The classifier (Classify.lean) determines their CRM level by type analysis.

  Author: Paul C.-K. Lee
  Date: February 2026
-/
import Lean

open Lean

namespace CRMLint.Infrastructure

/-- Check if `sub` occurs as a substring of `s`. -/
private def hasSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

-- ============================================================
-- § 1. BISH Infrastructure (genuinely constructive)
-- ============================================================

/-- Check if a name is genuinely BISH infrastructure.
    These are operations whose Classical.choice usage is a Lean/Mathlib
    artifact with no CRM content — the operation is constructively valid
    because the underlying types are discrete or finite.

    DOES NOT include: Real/Complex Decidable instances (these are WLPO),
    Classical.propDecidable/dec/decEq (these depend on what's being decided),
    Quotient.out/choice (these are CLASS). -/
def isBISHInfrastructure (name : Name) : Bool :=
  let s := toString name
  -- Decidable instances on DISCRETE types (genuinely BISH)
  hasSubstr s "instDecidableEqNat" ||
  hasSubstr s "instDecidableEqInt" ||
  hasSubstr s "instDecidableEqRat" ||
  hasSubstr s "instDecidableEqFin" ||
  hasSubstr s "instDecidableEqBool" ||
  hasSubstr s "instDecidableEqChar" ||
  hasSubstr s "instDecidableEqString" ||
  hasSubstr s "instDecidableLeNat" ||
  hasSubstr s "instDecidableLtNat" ||
  -- Linear order on discrete types (BISH)
  hasSubstr s "instLinearOrderNat" ||
  hasSubstr s "instLinearOrderInt" ||
  hasSubstr s "instLinearOrderRat" ||
  -- Fintype decidability (finite enumeration = BISH)
  hasSubstr s "Fintype.decidableEq" ||
  hasSubstr s "Fintype.decidableForall" ||
  hasSubstr s "Fintype.decidableExists" ||
  -- Boolean/Decidable kernel ops (BISH)
  hasSubstr s "Bool.decEq" ||
  -- Quotient CONSTRUCTION (not extraction!) — BISH
  hasSubstr s "Quot.mk" ||
  hasSubstr s "Quot.lift" ||
  hasSubstr s "Quot.ind" ||
  -- Lean kernel / grind tactic infrastructure
  hasSubstr s "Lean.Grind" ||
  hasSubstr s "Lean.trustCompiler"

-- ============================================================
-- § 2. Analytic Names (WLPO, not infrastructure)
-- ============================================================

/-- Check if a name involves Decidable on analytic types (ℝ, ℂ).
    These cost WLPO and must NOT be classified as infrastructure. -/
def isAnalyticDecidable (name : Name) : Bool :=
  let s := toString name
  hasSubstr s "instDecidableEqReal" ||
  hasSubstr s "instDecidableLeReal" ||
  hasSubstr s "instDecidableLtReal" ||
  hasSubstr s "instDecidableEqComplex" ||
  hasSubstr s "instLinearOrderReal" ||
  hasSubstr s "instLinearOrderedFieldReal" ||
  hasSubstr s "instLinearOrderedCommGroupWithZeroReal"

/-- Check if a name involves Classical choice/decidable generics.
    These are NOT infrastructure — their CRM cost depends on what proposition
    is being decided. The classifier (Classify.lean) must inspect the type. -/
def isClassicalDecidable (name : Name) : Bool :=
  let s := toString name
  hasSubstr s "Classical.propDecidable" ||
  hasSubstr s "Classical.dec" ||
  hasSubstr s "Classical.decEq" ||
  hasSubstr s "Decidable.decide"

/-- Check if a name involves quotient EXTRACTION (CLASS, not BISH).
    Quot.sound is constructive; Quotient.out and Quotient.choice are not. -/
def isQuotientExtraction (name : Name) : Bool :=
  let s := toString name
  hasSubstr s "Quotient.out" ||
  hasSubstr s "Quotient.choice" ||
  hasSubstr s "Quotient.recOnSubsingleton"

-- ============================================================
-- § 3. Explicit Name Whitelist
-- ============================================================

/-- Explicit infrastructure names: propext and Quot.sound.
    These carry zero CRM content in all contexts. -/
def infrastructureNameSet : NameSet :=
  NameSet.empty
    |>.insert ``propext
    |>.insert ``Quot.sound

-- ============================================================
-- § 4. Combined Classification
-- ============================================================

/-- Determine if a constant name is genuinely BISH infrastructure.
    Returns true ONLY for operations that are constructively valid
    regardless of context. Returns false for anything involving
    analytic types, classical generics, or quotient extraction —
    these require type-level analysis by the classifier. -/
def isInfrastructureName (name : Name) : Bool :=
  infrastructureNameSet.contains name || isBISHInfrastructure name

end CRMLint.Infrastructure
