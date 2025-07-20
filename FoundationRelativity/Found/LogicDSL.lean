/-!  Logic helpers (very small) -/

namespace Found
/-- Marker proposition: "This statement cannot be proved in BISH unless WLPO is assumed." -/
def RequiresWLPO (P : Prop) : Prop := P   -- initially just an alias

theorem RequiresWLPO.intro {P} (h : P) : RequiresWLPO P := h
end Found