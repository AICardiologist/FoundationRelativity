import Mathlib.Logic.IsEmpty
import LogicDSL.Core

/-!  Logic helpers (very small) -/

namespace Found
/-- Marker proposition: "This statement cannot be proved in BISH unless WLPO is assumed." -/
def RequiresWLPO (P : Prop) : Prop := P   -- initially just an alias

theorem RequiresWLPO.intro {P} (h : P) : RequiresWLPO P := h

/-- Marker proposition: "This statement requires countable dependent choice (DC_ω)." -/
def RequiresDCω (P : Prop) : Prop := P   -- For now, just an alias like RequiresWLPO

theorem RequiresDCω.intro {P} (h : P) : RequiresDCω P := h

/-- Marker proposition: "This statement requires dependent choice DC_{ω+1}." -/
def RequiresDCωPlus (P : Prop) : Prop := P   -- For now, just an alias like RequiresDCω

theorem RequiresDCωPlus.intro {P} (h : P) : RequiresDCωPlus P := h

/-- Marker proposition: "This statement requires countable axiom of choice (AC_ω)." -/
def RequiresACω (P : Prop) : Prop := P   -- For now, just an alias like RequiresDCω

theorem RequiresACω.intro {P} (h : P) : RequiresACω P := h

-- Re-export from LogicDSL.Core
open LogicDSL in
export LogicDSL (RequiresDCω3 WLPOPlusPlus dcω3_of_wlpoPlusPlus)

end Found