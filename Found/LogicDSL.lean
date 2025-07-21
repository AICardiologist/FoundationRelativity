import Mathlib.Logic.IsEmpty

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

end Found