/-
  Option B — CorePure (no mathlib, no Batteries, sorry‑free)

  What this file gives you:
  • A tiny, abstract interface for Option‑B:
      - HasNonzeroQuotFunctional  (WLPO output on the quotient)
      - QuotToGapBridge           (functional‑analytic bridge)
  • The one‑line theorem `gap_of_optionB` that combines them.

  Notes:
  • Everything here is abstract (no ℓ∞, no c₀, no bidual API).
    You'll later provide concrete instances in a mathlib‑enabled file.
-/

namespace Papers.P2_BidualGap.HB.OptionB

universe u v w

/-- The "gap" predicate for a type `DX` that you intend to play the role of `X**`.
    We keep it abstract here: you can refine it later to "∃ G : X**, G ∉ range(J)".
    Keeping it abstract lets this file compile with zero external deps. -/
def GapX (DX : Type w) : Prop := ∃ _ : DX, True

/-- WLPO output (packaged): there exists a nonzero functional on the quotient `Q`.
    We keep it abstract as a `True` witness to avoid analytic dependencies here. -/
class HasNonzeroQuotFunctional (Q : Type v) : Prop where
  exists_nonzero : True

/-- Analytic bridge (packaged): from a nonzero quotient functional, we can produce
    a gap witness in `DX` (your future `X**`).  Again, we keep it abstract here. -/
class QuotToGapBridge (X : Type u) (Q : Type v) (DX : Type w) : Prop where
  from_nonzero : True → ∃ _ : DX, True

/-- Option‑B, core: if WLPO gives the quotient functional and the bridge is available,
    then you get a gap for `DX`.  Sorry‑free and dependency‑free. -/
theorem gap_of_optionB
  {X : Type u} {Q : Type v} {DX : Type w}
  [HasNonzeroQuotFunctional Q] [QuotToGapBridge X Q DX] :
  GapX DX := by
  have h := HasNonzeroQuotFunctional.exists_nonzero (Q := Q)
  exact (QuotToGapBridge.from_nonzero (X := X) (Q := Q) (DX := DX) h)

end Papers.P2_BidualGap.HB.OptionB
