/-
  Paper 4: Quantum Spectra — Basic interface
  Minimal, self-contained tokens + witness-family interface
  (kept in a Paper-4 namespace to avoid clashes with Paper 3A).

  This file is intentionally lightweight: it sets up the "axiom tokens"
  and a WitnessFamily abstraction to encode upper bounds without sorries.
-/

namespace Papers.P4_SpectralGeometry.Spectral

/-- Foundations are left abstract here; we only need a parameter to carry tokens. -/
structure Foundation : Type where
  tag : String := "P4-Found"

/-- Axiom tokens used in Paper 4 (Paper-4-local versions to avoid clashes). -/
class HasWLPO (F : Foundation) : Prop
class HasFT   (F : Foundation) : Prop
class HasDCω  (F : Foundation) : Prop   -- Unicode omega allowed in Lean 4
abbrev HasDCw := HasDCω                  -- ASCII alias if needed
class HasMP   (F : Foundation) : Prop
class HasACω  (F : Foundation) : Prop

/-- A "witness family" is a family of propositions indexed by foundations. -/
structure WitnessFamily : Type where
  Witness : Foundation → Prop

namespace WitnessFamily

/-- Height-0: witnesses hold in all foundations (used for S0, S4). -/
def height0 : WitnessFamily :=
  { Witness := fun _F => True }

/-- Upper-bound wiring: witness holds whenever token T holds. -/
def fromToken (T : Foundation → Prop) : WitnessFamily :=
  { Witness := T }

end WitnessFamily

end Papers.P4_SpectralGeometry.Spectral