/-
  Papers/P2_BidualGap/Basic.lean
  
  Basic imports, notation, and helper tactics for Paper #2 "Bidual Gap"
-/

import CategoryTheory.BicatFound
import CategoryTheory.GapFunctor
import CategoryTheory.WitnessGroupoid.Core
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Group.Completeness

open CategoryTheory

namespace Papers.P2

-- Import the bicategory scaffold
open CategoryTheory.BicatFound

-- Import witness structures  
open CategoryTheory.WitnessGroupoid.Core

/-! ### Basic Definitions for Bidual Gap Analysis -/

/-- The bidual gap property: There exists a Banach space X such that 
    the canonical embedding X → X** is not surjective.
    
    The canonical embedding j : X → X** is defined by (j x)(φ) = φ(x)
    for x ∈ X and φ ∈ X*. The bidual gap occurs when this embedding
    is not onto, meaning there exist functionals in X** that are not
    evaluation functionals at points in X. -/
def BidualGap : Prop :=
  ∃ (X : Type*) (_ : NormedAddCommGroup X) (_ : NormedSpace ℝ X) (_ : CompleteSpace X),
  let canonical_embed := NormedSpace.inclusionInDoubleDual ℝ X
  ¬Function.Surjective canonical_embed

/-- Weak Limited Principle of Omniscience: For every sequence α : ℕ → Bool,
    either all values are false or not all values are false.
    
    This is a constructive logic principle that is weaker than the full
    Limited Principle of Omniscience (LPO) but still not provable in
    Bishop-style constructive mathematics (BISH). WLPO is equivalent
    to many classical theorems including the Hahn-Banach theorem and
    the existence of the bidual gap. -/
def WLPO : Prop := 
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ ¬(∀ n, α n = false)

/-! ### Helper Tactics for Banach Space Reasoning -/

-- Custom aesop rules for Banach / Gap reasoning
-- TODO Day 3: Expand with proper functional analysis automation
attribute [aesop safe apply] True.intro

end Papers.P2