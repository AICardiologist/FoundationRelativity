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
import Logic.Reflection

namespace Papers.P1_GBC

open Core Defs

/-- **Equivalence between syntactic consistency and truth of the Gödel
    sentence** – proved in `Logic/Reflection.lean` and re‑exported here. -/
theorem consistency_iff_G :
    consistencyPredicate peanoArithmetic ↔ GödelSentenceTrue :=
  reflection_equiv   -- already available; no `sorry`

/-! ### Gödel ⇔ Surjectivity equivalence -/

section GödelEquivalence
variable {g : ℕ}

/-- Helper lemma: When c_G = true, e_g is in the kernel of G -/
lemma e_g_in_ker_when_true (h : c_G = true) :
    e_g ∈ LinearMap.ker (G (g:=g)).toLinearMap := by
  simp [LinearMap.mem_ker, G, h, P_g_apply]
  -- When c_G = true, G = I - P_g
  -- So G(e_g) = e_g - P_g(e_g) = e_g - e_g = 0
  ext n
  by_cases hn : n = g
  · simp [hn, e_g_apply_self]
  · simp [hn, e_g_apply_ne hn]

/-- 1. Surjectivity ⇒ Gödel sentence *true*. -/
lemma surj_implies_false
    (h : Function.Surjective (G (g:=g)).toLinearMap) :
    c_G = false := by
  -- If `c_G = true` then `G = I − P_g` and has 1‑dim kernel,
  -- contradicting surjectivity. Use `G_inj_iff_surj`.
  by_contra hc
  push_neg at hc
  -- c_G must be true
  have hc_true : c_G = true := by
    cases h_c : c_G
    · contradiction
    · rfl
  -- Then e_g is in the kernel
  have h_ker : e_g ∈ LinearMap.ker (G (g:=g)).toLinearMap := 
    e_g_in_ker_when_true hc_true
  -- But G is surjective, so by Fredholm alternative it's injective
  have h_inj := (G_inj_iff_surj (g:=g)).mpr h
  -- Injective means trivial kernel
  have h_ker_trivial : LinearMap.ker (G (g:=g)).toLinearMap = ⊥ := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_bot]
    constructor
    · intro hx
      exact h_inj hx
    · intro hx
      simp [hx]
  -- This contradicts e_g being in the kernel (and e_g ≠ 0)
  have : e_g = 0 := by
    rw [← Submodule.mem_bot]
    rw [← h_ker_trivial]
    exact h_ker
  -- But e_g has norm 1, contradiction
  have : ‖e_g‖ = 0 := by simp [this]
  rw [e_g_norm] at this
  norm_num at this

/-- 2. Gödel sentence *true* ⇒ surjectivity of `G`. -/
lemma false_implies_surj (hG : c_G = false) :
    Function.Surjective (G (g:=g)).toLinearMap := by
  -- With `c_G = false` we literally have `G = 1`, trivial.
  have : G (g:=g) = 1 := by
    simp [G, hG]
  rw [this]
  simp only [ContinuousLinearMap.coe_id', LinearMap.id_coe]
  exact Function.surjective_id

/-- **Main equivalence.** (Surjective `G`) ↔ (Gödel bit = false). -/
theorem surjective_iff_false :
    Function.Surjective (G (g:=g)).toLinearMap ↔ c_G = false := by
  constructor
  · exact surj_implies_false
  · exact false_implies_surj

/-- Package the result into the statement file's name. -/
theorem godel_banach_main_correspondence :
    consistencyPredicate peanoArithmetic ↔
      Function.Surjective (G (g:=g)).toLinearMap := by
  -- Use the reflection lemma already in Core.lean
  have href : c_G = false ↔ GödelSentenceTrue := reflection_equiv
  -- Chain the equivalences
  rw [consistency_iff_G, ← href, surjective_iff_false]

end GödelEquivalence

end Papers.P1_GBC