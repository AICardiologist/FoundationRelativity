/-
  Papers/P3_2CatFramework/P4_Meta/ProofTheory/Core.lean
  
  Core infrastructure for proof-theoretic applications of AxCal.
  Provides typeclasses for arithmetized provability and derivability conditions.
-/

import Papers.P3_2CatFramework.P4_Meta.Meta_Signature

namespace Papers.P4Meta.ProofTheory

open Papers.P4Meta

/-- Sigma1 formulas (abstract predicate) -/
def Sigma1 : Formula → Prop := fun _ => True  -- Placeholder definition

/-- Implication for formulas (using atoms for simplicity) -/
def Formula.impl (φ ψ : Formula) : Formula := 
  Formula.atom (1000 + match φ, ψ with
    | Formula.atom n, Formula.atom m => n * 1000 + m)

/-! ## Arithmetization Infrastructure

We work schematically, treating arithmetization as a black box via typeclasses.
This avoids deep encoding while maintaining mathematical rigor.
-/

/-- Class for theories with arithmetized provability -/
class HasArithmetization (T : Theory) where
  /-- Codes formulas as natural numbers -/
  code : Formula → ℕ
  /-- Provability predicate as a formula -/
  provFormula : Formula → Formula
  /-- The provability predicate is Σ₁ -/
  prov_is_sigma1 : ∀ φ, Sigma1 (provFormula φ)

/-- Class for Σ₁ soundness/reflection -/
class HasSigma1Reflection (T : Theory) where
  /-- Σ₁ formulas represent arithmetic truths -/
  TrueInN : Formula → Prop
  /-- Bot is false in the standard model -/
  bot_false : ¬TrueInN Bot  -- Bot is false
  /-- Reflection: Σ₁ provability implies truth -/
  reflect : ∀ φ, Sigma1 φ → T.Provable φ → TrueInN φ

/-- Class for Hilbert-Bernays-Löb derivability conditions -/
class HasDerivability (T : Theory) extends HasArithmetization T where
  /-- D1: If T ⊢ φ then T ⊢ Prov(φ) -/
  derivability1 : ∀ φ, T.Provable φ → T.Provable (provFormula φ)
  /-- D2: T ⊢ Prov(φ → ψ) → Prov(φ) → Prov(ψ) -/
  derivability2 : ∀ φ ψ, T.Provable (Formula.impl (provFormula (Formula.impl φ ψ))
                          (Formula.impl (provFormula φ) (provFormula ψ)))
  /-- D3: T ⊢ Prov(φ) → Prov(Prov(φ)) -/
  derivability3 : ∀ φ, T.Provable (Formula.impl (provFormula φ) 
                                   (provFormula (provFormula φ)))

/-! ## Standard Theories -/

/-- Heyting Arithmetic (constructive base) -/
axiom HA : Theory

/-- Peano Arithmetic (classical) -/
axiom PA : Theory

/-- Elementary Arithmetic (weak base for metamathematics) -/
axiom EA : Theory

/-- IΣ₁ (another common weak base) -/
axiom ISigma1 : Theory

/-- HA is weaker than PA -/
axiom HA_weaker_PA : ∀ φ, HA.Provable φ → PA.Provable φ

/-- EA can formalize basic arithmetic (axiomatized) -/
axiom EA_has_arithmetization : HasArithmetization EA
axiom EA_has_derivability : HasDerivability EA

/-- PA satisfies all conditions (axiomatized) -/
axiom PA_has_arithmetization : HasArithmetization PA
axiom PA_has_derivability : HasDerivability PA

/-! ## Classical Principles -/

/-- Excluded middle for Σⁿ formulas -/
def EM_Sigma (n : Nat) : Formula := Formula.atom (500 + n)

/-- Classicality ladder: adding EM principles to HA -/
def ClassicalitySteps : Nat → Formula
| 0 => EM_Sigma 0  -- EM for Δ₀ (includes WLPO)
| n+1 => EM_Sigma (n+1)

/-- WLPO as a special case (height 1 on classicality axis) -/
def WLPO_formula : Formula := Formula.atom 311

/-- LPO (height 2 on classicality axis) -/  
def LPO_formula : Formula := Formula.atom 310

/-! ## Consistency and Gödel Sentences -/

/-- Bot as Formula.atom 0 -/
def Bot : Formula := Formula.atom (0 : Nat)

/-- Consistency statement for a theory -/
def ConsistencyFormula (T : Theory) [h : HasArithmetization T] : Formula :=
  Formula.atom (600 + h.code Bot)

/-- Gödel sentence for a theory -/
def GodelSentence (T : Theory) [h : HasArithmetization T] : Formula :=
  Formula.atom (700 + h.code Bot)

/-- Σ₁ reflection principle -/
def RFN_Sigma1_Formula (T : Theory) [h : HasArithmetization T] : Formula :=
  Formula.atom (800 + h.code Bot)


/-! ## Schematic Tag Formulas -/

/-- Schematic consistency tag at level n (not the actual Con formula) -/
abbrev ConTag (n : Nat) : Formula := Formula.atom (600 + n)

/-- Schematic reflection tag at level n (not the actual RFN formula) -/
abbrev RfnTag (n : Nat) : Formula := Formula.atom (800 + n)

/-- Schematic Gödel sentence tag at level n -/
abbrev GTagFormula (n : Nat) : Formula := Formula.atom (700 + n)

/-! ## Core Axioms -/

namespace Ax

/-- Bot is a Σ₁ formula.
    Provenance: Standard arithmetization, Bot is atomic. -/
axiom Sigma1_Bot : Sigma1 Bot

/-- Bot is false in the standard model.
    Provenance: Standard arithmetization, Bot codes falsity. -/
axiom Bot_is_FalseInN {T : Theory} [h : HasSigma1Reflection T] : 
  ¬h.TrueInN Bot

end Ax

-- Export for compatibility
export Ax (Sigma1_Bot Bot_is_FalseInN)

end Papers.P4Meta.ProofTheory