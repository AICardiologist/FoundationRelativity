/-
  Papers/P2_BidualGap/Logic/WLPOBasic.lean
  
  Basic WLPO definition that compiles cleanly.
-/

import Papers.P2_BidualGap.Basic

namespace Papers.P2_BidualGap

/-- A binary sequence -/
def BinarySeq := ℕ → Bool

/-- The Weak Limited Principle of Omniscience -/
def WLPO : Prop :=
  ∀ (α : BinarySeq), (∀ n, α n = false) ∨ ¬(∀ n, α n = false)

end Papers.P2_BidualGap