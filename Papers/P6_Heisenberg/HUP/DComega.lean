/-
Paper 6 — Dependent Choice (DCω) eliminator for serial relations.
Prop-only: no instances or executable defs.
-/

namespace Papers.P6_Heisenberg.HUP

/-- A serial relation: every node has a successor. -/
structure SerialRel (α : Type) : Type where
  R      : α → α → Prop
  serial : ∀ a, ∃ b, R a b

/-- Foundation type for AxCal framework compatibility -/  
axiom Foundation : Type

/-- DCω capability token -/
class HasDCω (F : Foundation) : Prop

/-- DCω builds an infinite sequence along any serial relation, from any seed. -/
axiom dcω_stream {F : Foundation} [HasDCω F]
  {α : Type} (S : SerialRel α) (a0 : α) :
  ∃ f : Nat → α, f 0 = a0 ∧ ∀ n, S.R (f n) (f (n+1))

end Papers.P6_Heisenberg.HUP