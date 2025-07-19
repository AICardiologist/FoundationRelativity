/-
  Guarded interpretation ι_guard : ZFC ⟶ G‑TT   (skeleton)
-/
import Found.Disc
import Found.FibRep
import Mathlib.CategoryTheory.Functor.Category

open CategoryTheory
universe u

abbrev SetCat := Type u
abbrev SSet   := SimplicialObject SetCat

/-- A *stub* for the delay ("later") modality on simplicial sets. -/
structure Delay where
  delay                       : SSet ⥤ SSet
  θ                           : 𝟭 SSet ⟶ delay
  delay_is_left_exact         : True
  delay_is_weak_one_truncate  : True

namespace Delay
def identityDelay : Delay := by
  refine { delay := 𝟭 _, θ := NatTrans.id _, delay_is_left_exact := ?_, delay_is_weak_one_truncate := ?_ } <;> trivial
end Delay

def baseObj : SetCat ⥤ SSet :=
  (FibRep.identityFibRep).obj.comp (SimplicialObject.const _)

structure GuardedInterpretation where
  Fobj        : SetCat ⥤ SSet
  delayF      : Delay
  preserves_Pi       : True
  preserves_Sigma    : True
  preserves_Id       : True
  commutes_with_delay : True

def iota_guard : GuardedInterpretation := by
  refine
  { Fobj                 := baseObj
    delayF               := Delay.identityDelay
    preserves_Pi         := ?_
    preserves_Sigma      := ?_
    preserves_Id         := ?_
    commutes_with_delay  := ?_ } <;> trivial

#eval (iota_guard.Fobj.obj ℕ).obj (SimplexCategory.mk 0)