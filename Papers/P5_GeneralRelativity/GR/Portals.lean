/-
Paper 5: General Relativity AxCal Analysis - Portal Framework (minimal, no-sorry version)
-/
import Papers.P5_GeneralRelativity.AxCalCore.Axis
import Papers.P5_GeneralRelativity.AxCalCore.Tokens

namespace Papers.P5_GeneralRelativity
open AxisProfile

-- Proof-route flags
inductive PortalFlag
| uses_zorn
| uses_limit_curve
| uses_serial_chain
| uses_reductio
deriving Repr, DecidableEq

-- Minimal usage predicate
def Uses (_ : PortalFlag) : Prop := True

-- Tiny, mathlib-free boolean membership for PortalFlag
def eqb (a b : PortalFlag) : Bool := decide (a = b)

def memFlag (f : PortalFlag) : List PortalFlag → Bool
| []      => false
| g :: gs => if eqb f g then true else memFlag f gs

-- Closed-form route-to-profile (component-wise)
def route_to_profile (flags : List PortalFlag) : AxisProfile :=
  { hChoice := if memFlag .uses_zorn flags then Height.one else Height.zero
  , hComp   := if memFlag .uses_limit_curve flags then Height.one else Height.zero
  , hLogic  := if (memFlag .uses_serial_chain flags || memFlag .uses_reductio flags)
               then Height.one else Height.zero }

-- Portal soundness axioms (signatures only; proofs in the paper)
axiom Zorn_portal      : ∀ {F : Foundation}, Uses .uses_zorn        → HasAC   F
axiom LimitCurve_portal: ∀ {F : Foundation}, Uses .uses_limit_curve → (HasFT F ∨ HasWKL0 F)
axiom SerialChain_portal :
  ∀ {F : Foundation} {X : Type} (R : X → X → Prop),
    Uses .uses_serial_chain → HasDCω F → (∀ x, ∃ y, R x y) →
    ∀ x₀, ∃ f : Nat → X, f 0 = x₀ ∧ ∀ n, R (f n) (f (n+1))
axiom Reductio_portal  : ∀ {F : Foundation}, Uses .uses_reductio    → HasLEM  F

end Papers.P5_GeneralRelativity