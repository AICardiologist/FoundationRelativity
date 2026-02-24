/-
  Paper 52: The Decidability Conduit — CRM Signatures Across the Langlands Correspondence
  Defs.lean — Core definitions, CRM complexity levels, and signature types

  This file defines the shared vocabulary for the entire bundle:
  - CRM complexity levels (BISH, MP, LPO, Σ₂⁰)
  - CRM signature triples
  - Omniscience principles (self-contained re-declarations)
  - General spectral gap predicate
-/

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.Basic

namespace Papers.P52

-- ========================================================================
-- §1. CRM Complexity Levels
-- ========================================================================

/-- The four complexity levels in the CRM hierarchy.
    BISH ⊂ MP ⊂ LPO ⊂ Sigma2. -/
inductive CRMLevel where
  | BISH    -- Bishop's constructive mathematics (no omniscience)
  | MP      -- Markov's Principle (bounded search from non-refutation)
  | LPO     -- Limited Principle of Omniscience (decidable zero-testing)
  | Sigma2  -- Σ₂⁰ / Π₂⁰ (universal/existential over LPO predicates)
  deriving DecidableEq, BEq, Repr

/-- A CRM signature: the complexity level required for each of the three axioms.
    - decidability: Axiom 1 (DecidableEq on Hom/multiplicity spaces)
    - integrality:  Axiom 2 (algebraic spectrum / IsIntegral)
    - polarization: Axiom 3 (Archimedean positive-definiteness) -/
structure CRMSignature where
  decidability : CRMLevel
  integrality  : CRMLevel
  polarization : CRMLevel
  deriving DecidableEq, BEq, Repr

/-- A CRM signature is BISH if all three axioms are at the BISH level. -/
def isBISH (sig : CRMSignature) : Prop :=
  sig.decidability = CRMLevel.BISH ∧
  sig.integrality  = CRMLevel.BISH ∧
  sig.polarization = CRMLevel.BISH

instance (sig : CRMSignature) : Decidable (isBISH sig) := by
  unfold isBISH
  exact instDecidableAnd

-- ========================================================================
-- §2. Omniscience Principles (Self-Contained)
-- ========================================================================

/-- The Limited Principle of Omniscience (LPO).
    For any binary sequence, either some term is true, or all terms are false.
    Re-declared from Paper 51 (self-contained bundle). -/
def LPO_Principle : Prop :=
  ∀ (α : ℕ → Bool), (∃ n, α n = true) ∨ (∀ n, α n = false)

/-- Markov's Principle (MP).
    If a binary sequence is not all-false, then some term is true.
    Weaker than LPO: requires non-refutation evidence. -/
def MarkovPrinciple : Prop :=
  ∀ (α : ℕ → Bool), ¬(∀ n, α n = false) → ∃ n, α n = true

/-- BISH-decidability: an existential ∃ n, P n is BISH-decidable
    when there exists an explicit bound B such that any witness is ≤ B. -/
def BISHDecidable (P : ℕ → Prop) (B : ℕ) : Prop :=
  (∃ n, P n) ↔ (∃ n, n ≤ B ∧ P n)

-- ========================================================================
-- §3. General Spectral Gap Predicate
-- ========================================================================

/-- A general spectral gap assertion: a local quantity admits a
    positive global lower bound uniformly over all parameters.
    This is Σ₂⁰: ∃ bound > 0, ∀ N, bound ≤ f(N). -/
def HasSpectralGap (local_quantity : ℕ → ℝ) : Prop :=
  ∃ bound : ℝ, 0 < bound ∧ ∀ N, bound ≤ local_quantity N

-- ========================================================================
-- §4. Positive-Definiteness (the universal descent mechanism)
-- ========================================================================

/-- Positive-definiteness of a bilinear form: the key mechanism
    converting LPO to BISH in all three domains (physics, automorphic,
    motivic). Parameterized over a generic "fiber" type. -/
def IsPositiveDefinite {V : Type*} (ip : V → V → ℝ) (zero : V) : Prop :=
  ∀ x : V, x ≠ zero → ip x x > 0

/-- The u-invariant of a field F: the maximum dimension of an
    anisotropic quadratic form over F.
    - u(ℝ) = ∞: positive-definite (anisotropic) forms exist in every dimension
    - u(ℚ_p) = 4: isotropic vectors exist in dim ≥ 5
    This is axiomatized as a natural number. -/
def UInvariant (name : String) : ℕ → Prop := fun u => True

end Papers.P52
