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
example : mk _ A ⊓ mk _ B = 
          mk _ (A ∩ B) := by
  simp [mk_inf_mk]

example : mk _ A ⊔ mk _ B = 
          mk _ (A ∪ B) := by
  simp [mk_sup_mk]

example : (mk _ A)ᶜ = mk _ Aᶜ := by
  simp [mk_compl]

example : mk _ A \ mk _ B = 
          mk _ (A \ B) := by
  simp [mk_sdiff_mk]

-- Test order with subset
example : mk _ A ≤ mk _ (A ∪ B) := by
  apply mk_le_mk_of_subset
  exact Set.subset_union_left

-- Test Boolean algebra laws
example : mk _ A ⊓ (mk _ B ⊔ mk _ (A ∪ B)) = 
          (mk _ A ⊓ mk _ B) ⊔ 
          (mk _ A ⊓ mk _ (A ∪ B)) := 
  inf_sup_left

example : (mk _ A ⊔ mk _ B)ᶜ = 
          (mk _ A)ᶜ ⊓ (mk _ B)ᶜ :=
  compl_sup

example : ((mk _ A)ᶜ)ᶜ = mk _ A :=
  compl_compl

end BasicTests

section ConcreteTests

-- Create a simple Boolean ideal for testing
def testIdeal : BoolIdeal where
  mem := {S | S.Finite}  -- finite sets form a Boolean ideal
  empty_mem := Set.finite_empty
  union_mem := fun hA hB => Set.Finite.union hA hB
  downward := fun h₁ h₂ => Set.Finite.subset h₂ h₁

variable {𝓘' : BoolIdeal := testIdeal}

-- Test with concrete sets
def A₁ : Set ℕ := {1, 2, 3}
def A₂ : Set ℕ := {2, 3, 4}

-- Test that operations compute correctly
example : @mk testIdeal A₁ ⊓ @mk testIdeal A₂ = @mk testIdeal {2, 3} := by
  simp [mk_inf_mk, A₁, A₂]
  rfl

example : @mk testIdeal A₁ ⊔ @mk testIdeal A₂ = @mk testIdeal {1, 2, 3, 4} := by
  simp [mk_sup_mk, A₁, A₂]
  rfl

end ConcreteTests

section AbstractProperties

variable {𝓘 : BoolIdeal}

-- Test that quotient respects the ideal
example (A B : Set ℕ) (h : (A △ B) ∈ 𝓘.mem) :
  mk _ A = mk _ B :=
  mk_eq_of_sdiff_mem _ h

-- Test standard Boolean algebra properties
example (x y : PowQuot 𝓘) : x ⊔ (x ⊓ y) = x := sup_inf_self
example (x y : PowQuot 𝓘) : x ⊓ (x ⊔ y) = x := inf_sup_self
example (x : PowQuot 𝓘) : x ⊔ xᶜ = ⊤ := sup_compl_eq_top
example (x : PowQuot 𝓘) : x ⊓ xᶜ = ⊥ := inf_compl_eq_bot
example (x : PowQuot 𝓘) : x ≤ ⊤ := le_top
example (x : PowQuot 𝓘) : ⊥ ≤ x := bot_le

end AbstractProperties

#print "✅ All clean sanity tests pass!"