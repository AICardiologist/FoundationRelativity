import Mathlib.Topology.Baire
import Papers.P3C_DCwAxis.DCw_Frontier_Interface

/-!
  Paper 3C: Mathlib binding for BaireNN token.
  
  This file is for nightly CI only, not for the main build.
  It binds the opaque BaireNN token to mathlib's BaireSpace.
-/

namespace Papers.P3C.DCw

/-- Bind the opaque token to mathlib's BaireSpace on ℕ^ℕ. -/
axiom BaireNN_of_mathlib : BaireSpace (Nat → Nat) → BaireNN
axiom mathlib_of_BaireNN : BaireNN → BaireSpace (Nat → Nat)

end Papers.P3C.DCw