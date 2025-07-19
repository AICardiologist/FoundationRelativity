import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

inductive Foundation where
  | bish    -- constructive setting (BISH)  
  | zfc     -- classical setting (ZFC)
deriving DecidableEq

open Foundation

/-- Interpretations between foundations -/
inductive Interp : Foundation → Foundation → Type
  | id_bish : Interp bish bish
  | id_zfc  : Interp zfc  zfc
  | forget  : Interp bish zfc          -- constructive ↦ classical
deriving DecidableEq

/-- Foundation as a small category with Interp as morphisms -/
instance : SmallCategory Foundation where
  Hom := Interp
  id := by
    intro F; cases F with
    | bish => exact Interp.id_bish
    | zfc  => exact Interp.id_zfc
  comp := by
    intro F G H f g
    cases f with
    | id_bish =>
      cases g with
      | id_bish => exact Interp.id_bish
      | forget => exact Interp.forget
    | id_zfc =>
      cases g with
      | id_zfc => exact Interp.id_zfc
    | forget =>
      cases g with
      | id_zfc => exact Interp.forget
  id_comp := by
    intro F G f
    cases f with
    | id_bish => rfl
    | id_zfc => rfl
    | forget => rfl
  comp_id := by
    intro F G f
    cases f with
    | id_bish => rfl
    | id_zfc => rfl
    | forget => rfl
  assoc := by
    intro F G H I f g h
    cases f <;> cases g <;> cases h <;> rfl

/-- Class guards for logical principles. -/
class HasHB (F : Foundation) : Prop where hahn_banach : True
class CountableChoice (F : Foundation) : Prop where DCω : True

instance : HasHB zfc := ⟨trivial⟩
instance : CountableChoice zfc := ⟨trivial⟩