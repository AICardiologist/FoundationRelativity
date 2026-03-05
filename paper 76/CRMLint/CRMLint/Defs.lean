/-
  CRMLint — Definitions
  Paper 76 of the Constructive Reverse Mathematics Series

  Canonical CRMLevel type (previously duplicated across P68, P70, P72–P75)
  plus audit result types for the automated CRM classifier.

  The CRM hierarchy:
    BISH ⊂ BISH+MP ⊂ BISH+LLPO ⊂ BISH+WLPO ⊂ BISH+LPO ⊂ CLASS

  Author: Paul C.-K. Lee
  Date: February 2026
-/
import Lean

open Lean

-- ============================================================
-- § 1. CRM Hierarchy (canonical definition)
-- ============================================================

inductive CRMLevel : Type where
  | BISH    : CRMLevel
  | BISH_MP : CRMLevel
  | LLPO    : CRMLevel
  | WLPO    : CRMLevel
  | LPO     : CRMLevel
  | CLASS   : CRMLevel
  deriving DecidableEq, Repr, BEq, Hashable, Inhabited

namespace CRMLevel

def toNat : CRMLevel → Nat
  | BISH    => 0
  | BISH_MP => 1
  | LLPO    => 2
  | WLPO    => 3
  | LPO     => 4
  | CLASS   => 5

instance : LE CRMLevel where
  le a b := a.toNat ≤ b.toNat

instance : LT CRMLevel where
  lt a b := a.toNat < b.toNat

instance (a b : CRMLevel) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

instance (a b : CRMLevel) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toNat < b.toNat))

def join (a b : CRMLevel) : CRMLevel :=
  if a.toNat ≤ b.toNat then b else a

instance : ToString CRMLevel where
  toString
    | BISH    => "BISH"
    | BISH_MP => "BISH+MP"
    | LLPO    => "BISH+LLPO"
    | WLPO    => "BISH+WLPO"
    | LPO     => "BISH+LPO"
    | CLASS   => "CLASS"

end CRMLevel

-- ============================================================
-- § 2. Classical Pattern Classification
-- ============================================================

/-- Classification of how a classical axiom enters a proof.
    Each pattern maps to a CRM level. -/
inductive ClassicalPattern where
  | decidableRealEq    -- Decidable on ℝ equality/comparison → WLPO
  | decidableExists    -- Decidable ∃ on infinite domain → LPO
  | zorn               -- Through Zorn's lemma / zorn_preorder → CLASS
  | wellOrder          -- Through well-ordering / IsWellOrder → CLASS
  | emSigma01          -- Classical.em on Σ⁰₁ predicate → MP
  | realInfrastructure -- ℝ field/order construction artifact → BISH
  | propextInfra       -- propext (always infrastructure) → BISH
  | quotSoundInfra     -- Quot.sound (always infrastructure) → BISH
  | unclassified       -- Unknown pattern → CLASS (conservative)
  deriving Repr, BEq, Inhabited

namespace ClassicalPattern

def toCRMLevel : ClassicalPattern → CRMLevel
  | decidableRealEq    => .WLPO
  | decidableExists    => .LPO
  | zorn               => .CLASS
  | wellOrder          => .CLASS
  | emSigma01          => .BISH_MP
  | realInfrastructure => .BISH
  | propextInfra       => .BISH
  | quotSoundInfra     => .BISH
  | unclassified       => .CLASS

def isInfrastructure : ClassicalPattern → Bool
  | realInfrastructure => true
  | propextInfra       => true
  | quotSoundInfra     => true
  | _                  => false

instance : ToString ClassicalPattern where
  toString
    | decidableRealEq    => "Decidable(ℝ eq/ord) → WLPO"
    | decidableExists    => "Decidable(∃) on infinite → LPO"
    | zorn               => "Zorn → CLASS"
    | wellOrder          => "WellOrder → CLASS"
    | emSigma01          => "EM on Σ⁰₁ → MP"
    | realInfrastructure => "ℝ infrastructure → BISH"
    | propextInfra       => "propext → BISH"
    | quotSoundInfra     => "Quot.sound → BISH"
    | unclassified       => "unclassified → CLASS"

end ClassicalPattern

-- ============================================================
-- § 3. Audit Result Types
-- ============================================================

/-- Role of a classical entry: infrastructure artifact or essential content. -/
inductive EntryRole where
  | infrastructure
  | essential
  deriving Repr, BEq, Inhabited

instance : ToString EntryRole where
  toString
    | .infrastructure => "infrastructure"
    | .essential      => "ESSENTIAL"

/-- A single classical axiom entry point in a proof's dependency graph. -/
structure ClassicalEntry where
  axiomName  : Name
  callerName : Name
  pattern    : ClassicalPattern
  role       : EntryRole
  deriving Repr

/-- Full CRM audit result for a single declaration. -/
structure CRMAuditResult where
  declName            : Name
  totalClassicalDeps  : Nat
  entries             : Array ClassicalEntry
  infrastructureCount : Nat
  essentialCount      : Nat
  level               : CRMLevel
  deriving Repr

-- ============================================================
-- § 4. Namespace Scan Summary
-- ============================================================

/-- Summary statistics from scanning an entire namespace. -/
structure NamespaceSummary where
  namespace_    : Name
  totalDecls    : Nat
  /-- Counts per CRM level. -/
  bishCount     : Nat
  bishMPCount   : Nat
  llpoCount     : Nat
  wlpoCount     : Nat
  lpoCount      : Nat
  classCount    : Nat
  /-- Declarations with highest essential classical content. -/
  hotspots      : Array (Name × CRMLevel × Nat)  -- (name, level, essentialCount)
  deriving Repr
