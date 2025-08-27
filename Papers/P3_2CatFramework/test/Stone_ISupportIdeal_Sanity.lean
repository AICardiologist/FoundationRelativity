/-
  Sanity: support ideal is an Ideal of (ℕ → R) under pointwise operations.
-/
import Papers.P3_2CatFramework.P4_Meta.StoneWindow_SupportIdeals
import Mathlib.RingTheory.Ideal.Basic

open Papers.P4Meta.StoneSupport
open Classical

noncomputable section

def 𝓘 : BoolIdeal := FinIdeal

-- Choose any semiring; `ℤ` works fine as a ring (hence semiring).
example : Ideal (Linf ℤ) := ISupportIdeal (R := ℤ) 𝓘

example (x y : Linf ℤ)
    (hx : supp' (R := ℤ) x ∈ 𝓘.mem)
    (hy : supp' (R := ℤ) y ∈ 𝓘.mem) :
    (x + y) ∈ ISupportIdeal (R := ℤ) 𝓘 := by
  -- By design, `mem` is exactly the support-in-𝓘 predicate.
  have : supp' (R := ℤ) (x + y) ⊆ supp' (R := ℤ) x ∪ supp' (R := ℤ) y :=
    supp'_add_subset (R := ℤ) x y
  -- Ideal closure (downward + union).
  exact (𝓘.downward this (𝓘.union_mem hx hy))

example (c : Linf ℤ) (x : Linf ℤ)
    (hx : supp' (R := ℤ) x ∈ 𝓘.mem) :
    (c * x) ∈ ISupportIdeal (R := ℤ) 𝓘 := by
  have : supp' (R := ℤ) (c * x) ⊆ supp' (R := ℤ) x :=
    supp'_mul_left_subset (R := ℤ) c x
  exact (𝓘.downward this hx)