/-
Paper 6 — Dependent Choice (DCω) eliminator for serial relations.
Prop-only: no instances or executable defs.
-/
import Papers.P6_Heisenberg.HUP.AxCalCore

namespace Papers.P6_Heisenberg.HUP
open Papers.P6_Heisenberg.HUP  -- brings Foundation, HasDCω into scope from AxCalCore

/-- A serial relation: every node has a successor. -/
structure SerialRel (α : Type) : Type where
  R      : α → α → Prop
  serial : ∀ a, ∃ b, R a b

/-- DCω builds an infinite sequence along any serial relation, from any seed. -/
axiom dcω_stream {F : Foundation} [HasDCω F]
  {α : Type} (S : SerialRel α) (a0 : α) :
  ∃ f : Nat → α, f 0 = a0 ∧ ∀ n, S.R (f n) (f (n+1))

end Papers.P6_Heisenberg.HUP