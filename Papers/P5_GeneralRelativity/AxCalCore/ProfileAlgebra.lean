/-
Paper 5: General Relativity AxCal Analysis - Profile Algebra (patch A)
ℰ-extensions + meet + DecidableEq + height parsing utilities
-/
import Papers.P5_GeneralRelativity.AxCalCore.Axis

namespace Papers.P5_GeneralRelativity

open AxisProfile
open Height

/-- Profiles form a meet-semilattice via componentwise min. -/
private def hmin : Height → Height → Height
| zero,  h     => zero  
| h,     zero  => zero
| one,   one   => one
| omega, _     => one   -- omega ⊓ anything = smallest common lower bound
| _,     omega => one

def meet (p q : AxisProfile) : AxisProfile :=
  { hChoice := hmin p.hChoice q.hChoice
  , hComp   := hmin p.hComp   q.hComp  
  , hLogic  := hmin p.hLogic  q.hLogic }

/-- ε-extensions: augment a profile with a height on a given axis. -/
def extend_choice (p : AxisProfile) (h : Height) : AxisProfile := 
  { p with hChoice := h }
  
def extend_comp (p : AxisProfile) (h : Height) : AxisProfile := 
  { p with hComp := h }
  
def extend_logic (p : AxisProfile) (h : Height) : AxisProfile := 
  { p with hLogic := h }

/-- Height parsing utilities. -/
def from_string_height : String → Option Height
| "0"     => some zero
| "1"     => some one  
| "ω"     => some omega
| "omega" => some omega
| _       => none

def to_string_height : Height → String
| zero  => "0"
| one   => "1" 
| omega => "ω"

/-- Profile display. -/
def to_string_profile (p : AxisProfile) : String :=
  s!"⟨{to_string_height p.hChoice}, {to_string_height p.hComp}, {to_string_height p.hLogic}⟩"

instance : ToString AxisProfile where
  toString := to_string_profile

/-- Instances for decidable equality (needed for memFlag, eqb). -/
instance : DecidableEq Height := by infer_instance
instance : DecidableEq AxisProfile := by infer_instance

end Papers.P5_GeneralRelativity