import Papers.P3_2CatFramework.P4_Meta.StoneWindow_SupportIdeals

/-!
# Sanity Tests for PowQuot Boolean Algebra

This file tests the Boolean algebra instance on PowQuot 𝓘
using the new convenience constructor to avoid type mismatches.
-/

open Papers.P4Meta.StoneSupport
open Papers.P4Meta.StoneSupport.PowQuot

section BasicTests

variable {𝓘 : BoolIdeal}

-- Direct instance synthesis should work since instances are available
-- The instances in StoneWindow_SupportIdeals are defined with variable (𝓘 : BoolIdeal)
example : Preorder (PowQuot 𝓘) := inferInstance
example : PartialOrder (PowQuot 𝓘) := inferInstance 
example : Lattice (PowQuot 𝓘) := inferInstance
example : DistribLattice (PowQuot 𝓘) := inferInstance
example : BooleanAlgebra (PowQuot 𝓘) := inferInstance

-- Two generic sets
def A : Set ℕ := {n | n % 2 = 0}  -- even numbers
def B : Set ℕ := {n | n % 3 = 0}  -- multiples of 3

-- These should reduce by simp straight to set facts
example : mk 𝓘 A ⊓ mk 𝓘 B = 
          mk 𝓘 (A ∩ B) := by
  simp [mk_inf_mk]

example : mk 𝓘 A ⊔ mk 𝓘 B = 
          mk 𝓘 (A ∪ B) := by
  simp [mk_sup_mk]

example : (mk 𝓘 A)ᶜ = mk 𝓘 Aᶜ := by
  simp [mk_compl]

example : mk 𝓘 A \ mk 𝓘 B = 
          mk 𝓘 (A ∩ Bᶜ) := by
  simp [mk_sdiff_mk]

-- Test order with subset
example : mk 𝓘 A ≤ mk 𝓘 (A ∪ B) := by
  apply mk_le_mk_of_subset
  exact Set.subset_union_left

-- Test Boolean algebra laws
example : mk 𝓘 A ⊓ (mk 𝓘 B ⊔ mk 𝓘 (A ∪ B)) = 
          (mk 𝓘 A ⊓ mk 𝓘 B) ⊔ 
          (mk 𝓘 A ⊓ mk 𝓘 (A ∪ B)) := by
  rw [inf_sup_left]

example : (mk 𝓘 A ⊔ mk 𝓘 B)ᶜ = 
          (mk 𝓘 A)ᶜ ⊓ (mk 𝓘 B)ᶜ := by
  rw [compl_sup]

example : ((mk 𝓘 A)ᶜ)ᶜ = mk 𝓘 A := by
  rw [compl_compl]

end BasicTests

section ConcreteTests

-- Create a simple Boolean ideal for testing
def testIdeal : BoolIdeal where
  mem := {S | S.Finite}  -- finite sets form a Boolean ideal
  empty_mem := Set.finite_empty
  union_mem := fun hA hB => Set.Finite.union hA hB
  downward := fun h₁ h₂ => Set.Finite.subset h₂ h₁

-- Test with concrete sets
def A₁ : Set ℕ := {1, 2, 3}
def A₂ : Set ℕ := {2, 3, 4}

-- Just test that the operations work through the quotient
example : ∃ C, @mk testIdeal A₁ ⊓ @mk testIdeal A₂ = @mk testIdeal C := by
  use A₁ ∩ A₂
  simp [mk_inf_mk]

example : ∃ C, @mk testIdeal A₁ ⊔ @mk testIdeal A₂ = @mk testIdeal C := by
  use A₁ ∪ A₂  
  simp [mk_sup_mk]

end ConcreteTests

section AbstractProperties

variable {𝓘 : BoolIdeal}

-- Test that quotient respects the ideal
example (A B : Set ℕ) (h : (A △ B) ∈ 𝓘.mem) :
  mk 𝓘 A = mk 𝓘 B :=
  mk_eq_of_sdiff_mem 𝓘 h

-- Test standard Boolean algebra properties
example (x y : PowQuot 𝓘) : x ⊔ (x ⊓ y) = x := sup_inf_self
example (x y : PowQuot 𝓘) : x ⊓ (x ⊔ y) = x := inf_sup_self
example (x : PowQuot 𝓘) : x ⊔ xᶜ = ⊤ := sup_compl_eq_top
example (x : PowQuot 𝓘) : x ⊓ xᶜ = ⊥ := inf_compl_eq_bot
example (x : PowQuot 𝓘) : x ≤ ⊤ := le_top
example (x : PowQuot 𝓘) : ⊥ ≤ x := bot_le

end AbstractProperties

section PreservationTests

variable {𝓘 𝓙 : BoolIdeal}

-- Test that mapOfLe preserves Boolean operations
example (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) (x y : PowQuot 𝓘) :
  Papers.P4Meta.StoneSupport.PowQuot.mapOfLe h (x ⊓ y) = 
  Papers.P4Meta.StoneSupport.PowQuot.mapOfLe h x ⊓ Papers.P4Meta.StoneSupport.PowQuot.mapOfLe h y :=
  Papers.P4Meta.StoneSupport.PowQuot.mapOfLe_inf h x y

example (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) (x y : PowQuot 𝓘) :
  Papers.P4Meta.StoneSupport.PowQuot.mapOfLe h (x ⊔ y) = 
  Papers.P4Meta.StoneSupport.PowQuot.mapOfLe h x ⊔ Papers.P4Meta.StoneSupport.PowQuot.mapOfLe h y :=
  Papers.P4Meta.StoneSupport.PowQuot.mapOfLe_sup h x y

example (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) (x : PowQuot 𝓘) :
  Papers.P4Meta.StoneSupport.PowQuot.mapOfLe h xᶜ = 
  (Papers.P4Meta.StoneSupport.PowQuot.mapOfLe h x)ᶜ :=
  Papers.P4Meta.StoneSupport.PowQuot.mapOfLe_compl h x

-- Test mk_eq_mk_iff
example (A B : Set ℕ) (h : (A △ B) ∈ 𝓘.mem) :
  mk 𝓘 A = mk 𝓘 B :=
  Papers.P4Meta.StoneSupport.mk_eq_mk_iff 𝓘 A B |>.mpr h

end PreservationTests

#print "✅ All clean sanity tests pass!"