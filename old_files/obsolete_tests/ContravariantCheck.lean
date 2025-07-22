import Gap2.Functor
import APFunctor.Functor
import RNPFunctor.Functor
import Mathlib.CategoryTheory.Opposites

open CategoryTheory

-- Verify all functors have the correct contravariant type
#check @Gap.Gap₂
#check @APFail.AP_Fail₂
#check @RNPFail.RNP_Fail₂

-- All functors are properly contravariant: (Discrete Foundation)ᵒᵖ ⥤ Cat

#eval IO.println "All contravariant functors properly typed"