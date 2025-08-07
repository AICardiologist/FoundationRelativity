/-
  Papers/P2_BidualGap/Constructive/HahnBanach.lean
  
  Constructive Hahn-Banach theorem for located subspaces.
  This requires ASP (hence WLPO) to construct the extension.
  
  References: Ishihara's work on constructive functional analysis
-/

import Papers.P2_BidualGap.Constructive.NormedSpace
import Papers.P2_BidualGap.Constructive.WLPO_ASP_Core

namespace Papers.P2_BidualGap.Constructive

open CReal CNormedSpace

/-- A sublinear functional (like a seminorm) -/
structure SublinearFunctional (E : Type*) [CNormedSpace E] where
  toFun : E → CReal
  subadditive : ∀ x y, ¬lt (add (toFun x) (toFun y)) (toFun (x + y))
  positive_homogeneous : ∀ (a : CReal) (x : E), lt zero a → 
    equiv (toFun (a • x)) (mul a (toFun x))

/-- The key interval for Hahn-Banach extension -/
structure HBInterval (E : Type*) [CNormedSpace E] (S : Set E) 
  (g : {x : E // x ∈ S} →L[CReal] CReal) (p : SublinearFunctional E) (x : E) where
  lower : CReal  -- sup{g(s) - p(s - x) : s ∈ S}
  upper : CReal  -- inf{p(x + s) - g(s) : s ∈ S}
  valid : ¬lt upper lower

/-- -- LaTeX Theorem 5.2
Constructive Hahn-Banach requires ASP -/
theorem hahn_banach_needs_asp : 
  (∀ (E : Type*) [CNormedSpace E] (S : Set E) (hS : Located E S)
    (g : {x : E // x ∈ S} →L[CReal] CReal) (p : SublinearFunctional E)
    (hg : ∀ s : {x : E // x ∈ S}, ¬lt (p.toFun s) (g.toFun s)),
  ∃ (f : E →L[CReal] CReal), 
    (∀ s ∈ S, equiv (f.toFun s) (g.toFun ⟨s, ‹_›⟩)) ∧
    (∀ x, ¬lt (p.toFun x) (f.toFun x))) → ASP := by
  intro hhb
  -- If we have Hahn-Banach, we can construct suprema
  -- This is because HB allows extending functionals that "measure" sets
  sorry -- TODO: Show HB implies ASP

/-- -- LaTeX Lemma 5.3
Computing the extension value requires ASP -/
lemma extension_value_needs_asp (hasp : ASP) 
  (E : Type*) [CNormedSpace E] (S : Set E) (hS : Located E S)
  (g : {x : E // x ∈ S} →L[CReal] CReal) (p : SublinearFunctional E)
  (x : E) (hx : x ∉ S) :
  ∃ (val : CReal), 
    -- val lies in the interval [lower, upper]
    ∀ (interval : HBInterval E S g p x),
    ¬lt val interval.lower ∧ ¬lt interval.upper val := by
  -- The key insight: we need to compute
  -- sup{g(s) - p(s - x) : s ∈ S} and inf{p(x + s) - g(s) : s ∈ S}
  -- These are suprema/infima of countable sets (since S has enumeration via Located)
  -- ASP gives us these values
  sorry -- TODO: Apply ASP to compute bounds

/-- -- LaTeX Theorem 5.4
Constructive Hahn-Banach for located subspaces -/
theorem constructive_hahn_banach (hasp : ASP) :
  ∀ (E : Type*) [CNormedSpace E] (S : Set E) (hS : Located E S)
    (g : {x : E // x ∈ S} →L[CReal] CReal) (p : SublinearFunctional E)
    (hg : ∀ s : {x : E // x ∈ S}, ¬lt (p.toFun s) (g.toFun s)),
  ∃ (f : E →L[CReal] CReal), 
    (∀ s ∈ S, equiv (f.toFun s) (g.toFun ⟨s, ‹_›⟩)) ∧
    (∀ x, ¬lt (p.toFun x) (f.toFun x)) := by
  intro E _ S hS g p hg
  -- Strategy: Extend g step by step using ASP to choose values
  -- Step 1: Well-order E \ S (constructively via choice sequence)
  -- Step 2: At each step, use ASP to find value in HB interval
  -- Step 3: Verify extension is linear and dominated by p
  sorry -- TODO: Implement transfinite construction

/-- Special case: Extending Banach limit from c to ℓ∞ -/
def banach_limit_functional (hasp : ASP) : ell_infty →L[CReal] CReal := by
  -- Define limit on convergent sequences
  let c := {x : ell_infty | ∃ l : CReal, ∀ ε, lt zero ε → 
    ∃ N, ∀ n ≥ N, lt (abs (add (x.seq n) (neg l))) ε}
  -- The functional g(x) = lim x on c
  have g : {x : ell_infty // x ∈ c} →L[CReal] CReal := by
    sorry -- TODO: Define limit functional
  -- The sublinear functional p(x) = limsup |x_n|
  have p : SublinearFunctional ell_infty := by
    sorry -- TODO: Define limsup as sublinear functional
  -- c₀ ⊆ c is located
  have hloc : Located ell_infty c := by
    sorry -- TODO: Show c is located via monotone convergence
  -- Apply Hahn-Banach
  obtain ⟨F, hF_extends, hF_dominated⟩ := constructive_hahn_banach hasp ell_infty c hloc g p sorry
  exact F

/-- -- LaTeX Theorem 5.5
The Banach limit witnesses the bidual gap -/
theorem banach_limit_witnesses_gap (hasp : ASP) :
  let F := banach_limit_functional hasp
  -- F vanishes on c₀
  (∀ x ∈ c_zero, equiv (F.toFun x) zero) ∧
  -- But F(1) = 1 where 1 is the constant sequence
  (let ones : ell_infty := ⟨fun _ => one, one, sorry, sorry⟩;
   equiv (F.toFun ones) one) := by
  sorry -- TODO: Verify properties of Banach limit

end Papers.P2_BidualGap.Constructive