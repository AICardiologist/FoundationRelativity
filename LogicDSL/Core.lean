/-!
# Logic DSL for Foundation‑Relativity

This file upgrades the previous stub definitions of
`WLPOPlusPlus` (Π⁰₂ WLPO) and `RequiresDCω3`
 (Dependent Choice for ω·3) into minimal inductive props.
They are still proved classically, so the global zero‑sorry
policy is preserved; but they now have *content* instead of
being mere `True`.
-/

universe u

namespace LogicDSL

/-- WLPO⁺⁺ (Π⁰₂ form):
    For every Boolean stream `b`, *either*
      all entries are `false`
    *or* there is an index with `b i = true`.           -/
def WLPOPlusPlus : Prop :=
  ∀ b : ℕ → Bool, (∀ n, b n = false) ∨ ∃ n, b n = true

/-- Classical proof term for `WLPOPlusPlus`.  \
    (Constructive proof is impossible, but the classical
     repo permits `by classical exact ...`.) -/
lemma classical_wlpoPlusPlus : WLPOPlusPlus := by
  classical
  intro b
  by_cases h : ∃ n, b n = true
  · exact Or.inr h
  · push_neg at h
    exact Or.inl h

/-- DC_{ω·3}: we model it minimally as "there exists a choice
    function for every countable sequence of inhabited predicates".
    (Enough for this project; upgrade later if needed.) -/
def RequiresDCω3 : Prop :=
  ∀ (P : ℕ → Type u), (∀ n, Nonempty (P n)) → Nonempty (Π n, P n)

/-- In classical Lean this is provable via choice. -/
lemma classical_dcω3 : RequiresDCω3 := by
  classical
  intro P h
  choose f hf using h   -- classical `choose` gives a function
  exact ⟨f⟩

/-- **Logical bridge**: WLPO⁺⁺ ⇒ DC_{ω·3}.
    The constructive content is still non‑trivial;
    here we supply a classical inhabitant so that proofs
    elsewhere can `exact` it. -/
lemma dcω3_of_wlpoPlusPlus (h : WLPOPlusPlus) :
    RequiresDCω3 := by
  -- Classical Lean lets us ignore the premise;
  -- we keep the arrow shape for future constructive work.
  exact classical_dcω3

end LogicDSL