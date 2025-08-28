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

-- Test mk_eq_mk_iff and mk_eq_mk
example (A B : Set ℕ) (h : (A △ B) ∈ 𝓘.mem) :
  mk 𝓘 A = mk 𝓘 B :=
  Papers.P4Meta.StoneSupport.mk_eq_mk_iff 𝓘 A B |>.mpr h

example (A B : Set ℕ) (h : (A △ B) ∈ 𝓘.mem) :
  mk 𝓘 A = mk 𝓘 B :=
  Papers.P4Meta.StoneSupport.mk_eq_mk 𝓘 A B h

-- Test monotonicity directly
example {𝓘 𝓙 : BoolIdeal}
  (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem)
  (A B : Set ℕ)
  (hAB : (A \ B) ∈ 𝓘.mem) :
  Papers.P4Meta.StoneSupport.PowQuot.mapOfLe h (mk 𝓘 A)
    ≤ Papers.P4Meta.StoneSupport.PowQuot.mapOfLe h (mk 𝓘 B) := by
  -- direct use of monotonicity; reduces to smallness under `h`
  have := Papers.P4Meta.StoneSupport.PowQuot.mapOfLe_monotone h
  apply this
  simpa [mk_le_mk] using hAB

end PreservationTests

-- Quick sanity checks for the new threshold lemmas
section ThresholdSanity
  variable {𝓘 : BoolIdeal} {A B : Set ℕ}

  example : (mk 𝓘 A = ⊥) ↔ A ∈ 𝓘.mem := Papers.P4Meta.StoneSupport.mk_eq_bot_iff A
  example : (mk 𝓘 A = ⊤) ↔ Aᶜ ∈ 𝓘.mem := Papers.P4Meta.StoneSupport.mk_eq_top_iff A

  example : mk 𝓘 A ⊓ mk 𝓘 B = ⊥ ↔ (A ∩ B) ∈ 𝓘.mem :=
    Papers.P4Meta.StoneSupport.mk_inf_eq_bot_iff A B

  example : mk 𝓘 A ⊔ mk 𝓘 B = ⊤ ↔ (Aᶜ ∩ Bᶜ) ∈ 𝓘.mem :=
    Papers.P4Meta.StoneSupport.mk_sup_eq_top_iff A B
end ThresholdSanity

-- Sanity checks for disjointness and complement lemmas
section DisjointComplSanity
  variable {𝓘 𝓙 : BoolIdeal} {A B : Set ℕ}

  example : Disjoint (mk 𝓘 A) (mk 𝓘 B) ↔ (A ∩ B) ∈ 𝓘.mem :=
    Papers.P4Meta.StoneSupport.disjoint_mk_iff A B

  example : IsCompl (mk 𝓘 A) (mk 𝓘 B) ↔ ((A ∩ B) ∈ 𝓘.mem ∧ (Aᶜ ∩ Bᶜ) ∈ 𝓘.mem) :=
    Papers.P4Meta.StoneSupport.isCompl_mk_iff A B

  -- Test mapOfLe preservation
  example (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) :
    Disjoint (PowQuot.mapOfLe h (mk 𝓘 A)) (PowQuot.mapOfLe h (mk 𝓘 B)) ↔
    (A ∩ B) ∈ 𝓙.mem :=
    Papers.P4Meta.StoneSupport.mapOfLe_disjoint_iff h A B

  example (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) :
    IsCompl (PowQuot.mapOfLe h (mk 𝓘 A)) (PowQuot.mapOfLe h (mk 𝓘 B)) ↔
    ((A ∩ B) ∈ 𝓙.mem ∧ (Aᶜ ∩ Bᶜ) ∈ 𝓙.mem) :=
    Papers.P4Meta.StoneSupport.mapOfLe_isCompl_iff h A B
end DisjointComplSanity

section BAHomTests

open Papers.P4Meta.StoneSupport

variable {𝓘 𝓙 𝓚 : BoolIdeal}

-- Test BAHom structure
example (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) :
  ∃ (f : BAHom (PowQuot 𝓘) (PowQuot 𝓙)), ∀ A, f (mk 𝓘 A) = mk 𝓙 A :=
  ⟨PowQuot.mapOfLeBAHom h, PowQuot.mapOfLeBAHom_apply_mk h⟩

-- Test composition
example (h₁ : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) (h₂ : ∀ S, S ∈ 𝓙.mem → S ∈ 𝓚.mem) :
  BAHom.comp (PowQuot.mapOfLeBAHom h₂) (PowQuot.mapOfLeBAHom h₁) = 
  PowQuot.mapOfLeBAHom (fun S hS => h₂ S (h₁ S hS)) :=
  PowQuot.mapOfLeBAHom_comp h₁ h₂

-- Test identity
example : PowQuot.mapOfLeBAHom (fun _ h => h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓘.mem) = BAHom.id :=
  PowQuot.mapOfLeBAHom_id

end BAHomTests

#print "✅ All clean sanity tests pass!"