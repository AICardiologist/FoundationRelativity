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

/-- Marker proposition: "This statement requires countable axiom of choice (AC_ω)." -/
def RequiresACω (P : Prop) : Prop := P   -- For now, just an alias like RequiresDCω

theorem RequiresACω.intro {P} (h : P) : RequiresACω P := h

/-- Marker proposition: "This statement requires dependent choice DC_{ω·3} (Π⁰₂-reflection)." -/
def RequiresDCω3 (P : Prop) : Prop := P   -- For Gödel-Gap pathology (ρ ≈ 4½-5)

theorem RequiresDCω3.intro {P} (h : P) : RequiresDCω3 P := h

/-- Enhanced WLPO (WLPO⁺⁺) for Π⁰₂ statements - placeholder for Day 3. -/
def WLPOPlusPlus (P : Prop) : Prop := P   -- Will be refined for Sel₃ impossibility

theorem WLPOPlusPlus.intro {P} (h : P) : WLPOPlusPlus P := h

end Found