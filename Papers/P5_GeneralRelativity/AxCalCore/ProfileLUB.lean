/-
  Paper 5: GR - Profile Algebra (axiom-free, ASCII-only)
-/
import Papers.P5_GeneralRelativity.AxCalCore.Axis

namespace Papers.P5_GeneralRelativity
open AxisProfile

def maxH (a b : Height) : Height :=
  match a, b with
  | Height.zero, h             => h
  | h,             Height.zero => h
  | Height.one,   Height.one   => Height.one
  | Height.one,   Height.omega => Height.omega
  | Height.omega, Height.one   => Height.omega
  | Height.omega, Height.omega => Height.omega

def maxH_comm (a b : Height) : maxH a b = maxH b a := by
  cases a <;> cases b <;> rfl

def maxH_assoc (a b c : Height) :
  maxH (maxH a b) c = maxH a (maxH b c) := by
  cases a <;> cases b <;> cases c <;> rfl

def maxH_idem (a : Height) : maxH a a = a := by
  cases a <;> rfl

def maxAP (p q : AxisProfile) : AxisProfile :=
  AxisProfile.mk
    (maxH p.hChoice q.hChoice)
    (maxH p.hComp   q.hComp)
    (maxH p.hLogic  q.hLogic)

def maxAP_hChoice (p q : AxisProfile) :
  (maxAP p q).hChoice = maxH p.hChoice q.hChoice := rfl
def maxAP_hComp (p q : AxisProfile) :
  (maxAP p q).hComp = maxH p.hComp q.hComp := rfl
def maxAP_hLogic (p q : AxisProfile) :
  (maxAP p q).hLogic = maxH p.hLogic q.hLogic := rfl

def maxAP_comm (p q : AxisProfile) : maxAP p q = maxAP q p := by
  cases p <;> cases q <;> simp [maxAP, maxH_comm]

def maxAP_assoc (p q r : AxisProfile) :
  maxAP (maxAP p q) r = maxAP p (maxAP q r) := by
  cases p <;> cases q <;> cases r <;> simp [maxAP, maxH_assoc]

def maxAP_idem (p : AxisProfile) : maxAP p p = p := by
  cases p <;> simp [maxAP, maxH_idem]

def maxH_if_one_zero (a b : Bool) :
  maxH (if a then Height.one else Height.zero)
       (if b then Height.one else Height.zero)
    = (if a || b then Height.one else Height.zero) := by
  cases a <;> cases b <;> rfl

@[simp] theorem maxAP_hChoice_simp (p q : AxisProfile) :
  (maxAP p q).hChoice = maxH p.hChoice q.hChoice := by
  simpa using maxAP_hChoice p q

@[simp] theorem maxAP_hComp_simp (p q : AxisProfile) :
  (maxAP p q).hComp = maxH p.hComp q.hComp := by
  simpa using maxAP_hComp p q

@[simp] theorem maxAP_hLogic_simp (p q : AxisProfile) :
  (maxAP p q).hLogic = maxH p.hLogic q.hLogic := by
  simpa using maxAP_hLogic p q

@[simp] theorem maxH_if_one_zero_simp (a b : Bool) :
  maxH (if a then Height.one else Height.zero)
       (if b then Height.one else Height.zero)
    = (if a || b then Height.one else Height.zero) := by
  simpa using maxH_if_one_zero a b

namespace AxisProfile
theorem ext {p q : AxisProfile}
  (hC : p.hChoice = q.hChoice)
  (hK : p.hComp   = q.hComp)
  (hL : p.hLogic  = q.hLogic) : p = q := by
  cases p; cases q; cases hC; cases hK; cases hL; rfl
end AxisProfile

attribute [ext] AxisProfile.ext

end Papers.P5_GeneralRelativity