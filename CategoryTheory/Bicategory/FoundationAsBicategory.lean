/-
  Make Foundation into a Bicategory instance by viewing it as a locally discrete bicategory.
  Since Foundation is already a Category, we can use LocallyDiscrete to get a strict bicategory.
-/
import CategoryTheory.PseudoFunctor
import Found.InterpCore
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

open CategoryTheory

/-- Foundation viewed as a locally discrete bicategory -/
abbrev FoundationBicat := LocallyDiscrete Foundation

/-- The identity pseudo-functor on Foundation (as a bicategory) -/
def FoundationIdPF : PseudoFunctor FoundationBicat FoundationBicat := 
  PseudoFunctor.id FoundationBicat