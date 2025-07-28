/-
Copyright 2025
Released under Apache 2.0 licence
Authors: Math‑AI

This file closes the main Gödel–Banach equivalence
for the rank‑one operator `G` introduced in `Core.lean`.
-/
import Papers.P1_GBC.Core
import Papers.P1_GBC.Defs
import Papers.P1_GBC.Statement   -- for theorem names

open Papers.P1_GBC Core

namespace Papers.P1_GBC

/-! ### Gödel ⇔ Surjectivity equivalence -/

variable {g : ℕ}

/-- 1.  Surjectivity ⇒ Gödel sentence *true*. -/
lemma surj_implies_G
    (h : Function.Surjective (G (g:=g)).toLinearMap) :
    c_G = false := by
  -- If `c_G = true` then `G = I − P_g` and has 1‑dim kernel,
  -- contradicting surjectivity.  Use `G_inj_iff_surj`.
  by_contra hc
  have hker : (LinearMap.ker (G (g:=g)).toLinearMap) ≠ ⊥ := by
    -- `e_g` lies in the kernel when `c_G`
    have : c_G = true := by
      cases c_G <;> simp at hc
    subst this
    have : (e_g (g:=g)) ∈ LinearMap.ker (G (g:=g)).toLinearMap := by
      simp [G, P_g_apply]
    intro hk
    have : (e_g (g:=g)) = 0 := by
      have := congrArg Subtype.val (Submodule.ext_iff.mp hk).mpr this
      simpa using this
    have : ‖e_g (g:=g)‖ = 0 := by simpa using congrArg _ this
    simpa [e_g_norm] using this
  -- Surjectivity ⇒ injectivity by Fredholm alternative
  have hinj := (G_inj_iff_surj (g:=g)).mpr h
  have hker_eq : LinearMap.ker (G (g:=g)).toLinearMap = ⊥ :=
    by
      -- injective ⇒ trivial kernel
      ext x; constructor
      · intro hx
        have : (G (g:=g)) x = 0 := hx
        have : x = 0 := by
          have := hinj this
          simpa using this
        simpa [this]
      · intro hx; simp [hx]
  exact (hker hker_eq).elim

/-- 2.  Gödel sentence *true* ⇒ surjectivity of `G`. -/
lemma G_implies_surj (hG : c_G = false) :
    Function.Surjective (G (g:=g)).toLinearMap := by
  -- With `c_G = false` we literally have `G = 1`, trivial.
  have : G (g:=g) = 1 := by
    simp [G, hG]
  simpa [this] using Function.surjective_id

/-- **Main equivalence.**  (Surjective `G`) ↔ (Gödel bit = false). -/
theorem surjective_iff_G_bool :
    Function.Surjective (G (g:=g)).toLinearMap ↔ c_G = false := by
  constructor
  · exact surj_implies_G (g:=g)
  · intro h; exact G_implies_surj (g:=g) h

/-- Package the result into the statement file's name. -/
theorem godel_banach_main
    (hg : g = g) :   -- placeholder param matches Statement.lean sig
    consistencyPredicate peanoArithmetic ↔
      Function.Surjective (G (g:=g)).toLinearMap := by
  -- For the sprint we use the reflection lemma already in Core.lean
  have href : c_G = false ↔ GödelSentenceTrue := reflection_equiv
  -- Combine:
  --   Consistency ↔ GödelSentenceTrue
  --   GödelSentenceTrue ↔ c_G = false
  --   c_G = false ↔ Surjective G   (proved above)
  --   → chain them.
  calc
    consistencyPredicate peanoArithmetic
        ↔ GödelSentenceTrue := consistency_iff_G (by simpa)
    _ ↔ c_G = false         := href.symm
    _ ↔ _                   := (surjective_iff_G_bool (g:=g)).symm

end Papers.P1_GBC