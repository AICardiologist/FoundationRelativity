/-
  Option B — Instances
  
  Minimal, dependency-free instances to exercise CorePure's theorem schema.
  This is purely schematic (dummy types); it proves the architecture works.
-/
import Papers.P2_BidualGap.HB.OptionB.CorePure

namespace Papers.P2_BidualGap.HB.OptionB.Instances

/-- Dummy stand-ins; no structure needed for this end-to-end check. -/
def X  : Type := Unit
def Q  : Type := Unit  -- The quotient X/C0
def DX : Type := Unit  -- The bidual X**

/-- Pretend WLPO/AC supplies a nonzero functional on X ⧸ C0. -/
instance : HasNonzeroQuotFunctional Q := ⟨trivial⟩

/-- Pretend the analytic bridge maps such a functional to a gap in X**. -/
instance : QuotToGapBridge X Q DX := ⟨fun _ => ⟨(), trivial⟩⟩

/-- One-line Option‑B consequence: we get the gap. -/
example : GapX DX := gap_of_optionB (X := X) (Q := Q) (DX := DX)

#check @gap_of_optionB X Q DX _ _  -- Verify the theorem applies

end Papers.P2_BidualGap.HB.OptionB.Instances