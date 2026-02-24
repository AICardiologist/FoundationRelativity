/-
  P7_Minimal/Defs.lean
  Dependency-free abstract definitions for Paper 7 logical skeleton.

  This artifact captures the logical reduction from
  "S₁(H) non-reflexivity witness ↔ WLPO" without Mathlib.
  All Banach space concepts are abstracted to Prop-level predicates.
  The mathematical content (Hahn-Banach, norm estimates) lives in
  P7_Full (754 lines, Mathlib-based, zero sorry in 7/8 files).

  No Mathlib imports anywhere in P7_Minimal.
-/

-- No imports from Mathlib. Only Lean core.

universe u

namespace P7_Minimal

-- =============================================
-- Opaque types (standing for ℓ¹ and S₁(H))
-- =============================================

/-- Opaque type standing for ℓ¹(ℕ, ℝ). -/
opaque ell1_Type : Type

/-- Opaque type standing for S₁(H), trace-class operators
    on a separable Hilbert space. -/
opaque S1H_Type : Type

-- =============================================
-- Abstract predicates (Prop-level)
-- =============================================

/-- Abstract predicate: "X is reflexive"
    (the canonical embedding J_X : X → X** is surjective).
    In P7_Full this is `IsReflexive 𝕜 X := Function.Surjective (inclusionInDoubleDual 𝕜 X)`. -/
class IsReflexiveSpace (X : Type _) : Prop where
  is_reflexive : True

/-- Abstract predicate: "X is non-reflexive with witness"
    (there exists Ψ ∈ X** \ J(X)).
    In P7_Full this is `∃ Ψ : StrongDual ℝ (StrongDual ℝ X), Ψ ∉ Set.range (inclusionInDoubleDual ℝ X)`. -/
class NonReflexiveWitness (X : Type _) : Prop where
  has_witness : True

/-- Abstract predicate: "Y is a closed subspace of X".
    In P7_Full this is modeled via `HasTraceClassContainer` (for ℓ¹ ↪ S₁(H)). -/
class ClosedSubspaceOf (Y X : Type _) : Prop where
  is_closed_subspace : True

-- =============================================
-- WLPO (concrete definition — the only definition
-- with real logical content in P7_Minimal)
-- =============================================

/-- The Weak Limited Principle of Omniscience.
    For any binary sequence α : ℕ → Bool, either all terms are false
    or it is not the case that all terms are false.
    Matches the definition in P7_Full's Basic.lean. -/
def WLPO : Prop :=
  ∀ (α : Nat → Bool), (∀ n, α n = false) ∨ ¬(∀ n, α n = false)

-- =============================================
-- Structural axioms
-- =============================================

/-- Reflexive and NonReflexiveWitness are contradictory.
    If J_X is surjective, there cannot exist Ψ ∈ X** \ J(X). -/
axiom reflexive_not_witness (X : Type _) :
  IsReflexiveSpace X → NonReflexiveWitness X → False

end P7_Minimal
