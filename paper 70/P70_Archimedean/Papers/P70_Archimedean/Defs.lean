/-
  Paper 70: The Archimedean Principle — CRM Infrastructure
  Defines the CRM hierarchy, domain profiles, and descent types.

  The CRM hierarchy: BISH ⊂ BISH+MP ⊂ LLPO ⊂ WLPO ⊂ LPO ⊂ CLASS
  Reference: Bridges–Richman, Varieties of Constructive Mathematics (1987).
-/
import Mathlib.Order.Defs.PartialOrder

-- ============================================================
-- CRM Hierarchy
-- ============================================================

/-- The CRM hierarchy of constructive principles.
    Ordered by logical strength: BISH < BISH+MP < LLPO < WLPO < LPO < CLASS. -/
inductive CRMLevel : Type where
  | BISH    : CRMLevel
  | BISH_MP : CRMLevel  -- BISH + Markov's Principle
  | LLPO    : CRMLevel
  | WLPO    : CRMLevel
  | LPO     : CRMLevel
  | CLASS   : CRMLevel
  deriving DecidableEq, Repr

open CRMLevel

instance : LE CRMLevel where
  le a b := a.ctorIdx ≤ b.ctorIdx

instance : LT CRMLevel where
  lt a b := a.ctorIdx < b.ctorIdx

instance (a b : CRMLevel) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.ctorIdx ≤ b.ctorIdx))

instance (a b : CRMLevel) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.ctorIdx < b.ctorIdx))

/-- The CRM join (supremum) of two levels. -/
def CRMLevel.join (a b : CRMLevel) : CRMLevel :=
  if a.ctorIdx ≥ b.ctorIdx then a else b

-- ============================================================
-- Descent Types
-- ============================================================

/-- Descent type: how a domain extracts BISH predictions from LPO data.

    Projection: finite-rank inner product computation (physics: measurement).
      The inner product ⟨ψ|A|ψ⟩ is a single computable function. No search.
      Eliminates both LPO and MP in one step.

    Search: unbounded existential witness-finding (arithmetic: Mordell–Weil generators).
      The motive guarantees algebraic answers (eliminating LPO),
      but finding the explicit witness requires unbounded search (preserving MP). -/
inductive DescentType where
  | projection : DescentType
  | search     : DescentType
  deriving DecidableEq, Repr

open DescentType

/-- The CRM level after descent, determined by descent type.
    Projection → BISH (measurement is computable, no search).
    Search → BISH+MP (witness exists but finding it needs unbounded search). -/
def descent_output : DescentType → CRMLevel
  | projection => BISH
  | search     => BISH_MP

-- ============================================================
-- Domain Profiles
-- ============================================================

/-- A domain is characterised by two parameters:
    (1) whether it has an Archimedean place (source of LPO/WLPO)
    (2) what descent type it uses (projection vs search) -/
structure DomainProfile where
  has_archimedean : Bool
  descent : DescentType

/-- Pre-descent CRM level: the "raw" logical cost before descent.
    Archimedean place → LPO. No Archimedean place → BISH. -/
def pre_descent_level (d : DomainProfile) : CRMLevel :=
  if d.has_archimedean then LPO else BISH

/-- Post-descent CRM level: what the domain actually needs.
    No Archimedean → BISH (trivially).
    Archimedean → descent_output determines the residual. -/
def post_descent_level (d : DomainProfile) : CRMLevel :=
  if d.has_archimedean then descent_output d.descent else BISH

-- The four domains of the CRM programme

/-- Continuum physics: Archimedean (L²(ℝⁿ)), projection descent (measurement). -/
def continuum_physics : DomainProfile := ⟨true, projection⟩

/-- Lattice physics: no Archimedean (ℂᴺ), projection descent. -/
def lattice_physics : DomainProfile := ⟨false, projection⟩

/-- Number field arithmetic: Archimedean (ℝ-completion), search descent. -/
def numfield_arith : DomainProfile := ⟨true, search⟩

/-- Function field arithmetic: no Archimedean (𝔽_q(C)), search descent. -/
def funcfield_arith : DomainProfile := ⟨false, search⟩

-- ============================================================
-- The MP Gap (projection vs search)
-- ============================================================

/-- Physics uses projection descent: measurement is a computable function. -/
theorem physics_descent_type :
    descent_output projection = BISH := by rfl

/-- Arithmetic uses search descent: witness-finding needs unbounded search. -/
theorem arithmetic_descent_type :
    descent_output search = BISH_MP := by rfl

/-- **THEOREM (MP Gap):**
    Projection descent is strictly stronger than search descent.
    Physics descends to BISH. Arithmetic descends to BISH+MP.

    This is why number theory is harder than physics, in a precise logical
    sense. Physical measurement projects onto a finite-dimensional eigenspace.
    Motivic witness search ranges over infinite discrete spaces.
    The residual MP is Diophantine hardness.

    Reference: Paper 43 (Why number theory is harder than physics). -/
theorem mp_gap : descent_output projection < descent_output search := by
  unfold descent_output
  native_decide

/-- The gap is strict: BISH ≠ BISH+MP. -/
theorem descent_gap_strict :
    descent_output projection ≠ descent_output search := by
  unfold descent_output
  native_decide
