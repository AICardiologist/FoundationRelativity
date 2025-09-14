/-
  Paper 5: GR - Portal Framework (cycle-free)
-/
import Papers.P5_GeneralRelativity.AxCalCore.Axis
import Papers.P5_GeneralRelativity.AxCalCore.Tokens

namespace Papers.P5_GeneralRelativity
open AxisProfile

inductive PortalFlag
| uses_zorn | uses_limit_curve | uses_serial_chain | uses_reductio
deriving Repr, DecidableEq

def Uses (_ : PortalFlag) : Prop := True

def eqb (a b : PortalFlag) : Bool := decide (a = b)

def memFlag (f : PortalFlag) : List PortalFlag -> Bool
| []      => false
| g :: gs => if eqb f g then true else memFlag f gs

def route_to_profile (flags : List PortalFlag) : AxisProfile :=
  AxisProfile.mk
    (if memFlag .uses_zorn        flags then Height.one else Height.zero)
    (if memFlag .uses_limit_curve flags then Height.one else Height.zero)
    (if (memFlag .uses_serial_chain flags || memFlag .uses_reductio flags)
      then Height.one else Height.zero)

-- Basic simp lemmas for list membership
@[simp] theorem memFlag_nil (f : PortalFlag) : memFlag f [] = false := rfl

@[simp] theorem memFlag_cons (f g : PortalFlag) (gs : List PortalFlag) :
  memFlag f (g :: gs) = if eqb f g then true else memFlag f gs := rfl

@[simp] theorem memFlag_append (f : PortalFlag) (xs ys : List PortalFlag) :
  memFlag f (xs ++ ys) = (memFlag f xs || memFlag f ys) := by
  induction xs with
  | nil => simp [memFlag]
  | cons g gs ih =>
      cases h : eqb f g <;> simp [memFlag, h, ih]

axiom Zorn_portal      : ∀ {F : Foundation}, Uses .uses_zorn        -> HasAC   F
axiom LimitCurve_portal: ∀ {F : Foundation}, Uses .uses_limit_curve -> (HasFT F ∨ HasWKL0 F)
axiom SerialChain_portal :
  ∀ {F : Foundation} {X : Type} (R : X -> X -> Prop),
    Uses .uses_serial_chain -> HasDCω F ->
    (∀ x, ∃ y, R x y) ->
    ∀ x0, ∃ f : Nat -> X, f 0 = x0 ∧ ∀ n, R (f n) (f (n+1))
axiom Reductio_portal  : ∀ {F : Foundation}, Uses .uses_reductio    -> HasLEM  F

end Papers.P5_GeneralRelativity