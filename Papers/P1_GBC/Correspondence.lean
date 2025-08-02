/-
Copyright 2025
Released under Apache 2.0 licence
Authors: Math‑AI

This file closes the main Gödel–Banach equivalence
for the rank‑one operator `G` introduced in `Core.lean`.
-/
import Papers.P1_GBC.Core
import Papers.P1_GBC.Defs
import Papers.P1_GBC.Statement
import Papers.P1_GBC.LogicAxioms
import Logic.Reflection

namespace Papers.P1_GBC

open Papers.P1_GBC.Defs
open AnalyticPathologies

/-- **Equivalence between syntactic consistency and truth of the Gödel
    sentence** – proved in `Logic/Reflection.lean` and re‑exported here. -/
theorem consistency_iff_G :
    consistencyPredicate peanoArithmetic ↔ GödelSentenceTrue :=
  -- Use the reflection equivalence from Core.lean
  by
    unfold consistencyPredicate GödelSentenceTrue
    -- Both sides are equivalent to c_G = false
    have h1 : consistencyPredicate peanoArithmetic ↔ (c_G = false) := by
      -- Use the axiomatized consistency characterization from LogicAxioms
      constructor
      · -- consistency → c_G = false
        intro h_cons
        -- By consistency_characterization: consistency ↔ ¬Provable G_formula
        have h_not_prov : ¬Arithmetic.Provable Arithmetic.G_formula := 
          LogicAxioms.consistency_characterization.mp h_cons
        -- By definition: c_G = decide (Provable G_formula)
        simp only [c_G, Arithmetic.c_G]
        exact decide_eq_false_iff_not.mpr h_not_prov
      · -- c_G = false → consistency
        intro h_cG_false
        -- By definition: c_G = false means ¬Provable G_formula
        have h_not_prov : ¬Arithmetic.Provable Arithmetic.G_formula := by
          simp only [c_G, Arithmetic.c_G] at h_cG_false
          exact decide_eq_false_iff_not.mp h_cG_false
        -- By consistency_characterization: ¬Provable G_formula → consistency
        exact LogicAxioms.consistency_characterization.mpr h_not_prov
    have h2 : GödelSentenceTrue ↔ (c_G = false) := by
      exact reflection_equiv.symm
    exact h1.trans h2.symm

/-! ### Gödel ⇔ Surjectivity equivalence -/

section GödelEquivalence
variable {g : ℕ}

/-- Helper lemma: When c_G = true, e_g is in the kernel of G -/
lemma e_g_in_ker_when_true (h : c_G = true) :
    e_g (g:=g) ∈ LinearMap.ker (G (g:=g)).toLinearMap := by
  -- When c_G = true, G = I - P_g
  -- We need to show G(e_g) = 0
  rw [LinearMap.mem_ker]
  -- From Core.lean proof: G(e_g) = e_g - P_g(e_g) = e_g - e_g = 0
  simp [G, h, P_g, e_g]

/-- 1. Surjectivity ⇒ Gödel sentence *true*. -/
lemma surj_implies_false
    (h : Function.Surjective (G (g:=g)).toLinearMap) :
    c_G = false := 
  -- This is exactly the forward direction of G_surjective_iff_not_provable
  (G_surjective_iff_not_provable (g:=g)).mp h

/-- 2. Gödel sentence *true* ⇒ surjectivity of `G`. -/
lemma false_implies_surj (hG : c_G = false) :
    Function.Surjective (G (g:=g)).toLinearMap := 
  -- When c_G = false, G = I, which is surjective
  by
    have h_eq : G (g := g) = 1 := by
      simp [G, hG]
    rw [h_eq]
    exact Function.surjective_id

/-- **Main equivalence.** (Surjective `G`) ↔ (Gödel bit = false). -/
theorem surjective_iff_false :
    Function.Surjective (G (g:=g)).toLinearMap ↔ c_G = false := 
  ⟨surj_implies_false, false_implies_surj⟩

/-- Package the result into the statement file's name. -/
theorem godel_banach_main_correspondence :
    consistencyPredicate peanoArithmetic ↔
      Function.Surjective (G (g:=g)).toLinearMap := 
  -- Chain the equivalences
  -- consistencyPredicate ↔ GödelSentenceTrue ↔ (c_G = false) ↔ Surjective G
  calc consistencyPredicate peanoArithmetic 
    ↔ GödelSentenceTrue := consistency_iff_G
    _ ↔ (c_G = false) := reflection_equiv.symm
    _ ↔ Function.Surjective (G (g:=g)).toLinearMap := surjective_iff_false.symm

end GödelEquivalence

end Papers.P1_GBC