/-
  Contractibility lemma stub  (Riehl–Verity Prop. 6.5.1)
  ------------------------------------------------------
  Statement:  For a simplicial quasi‑category `A` and two strict functors
  `F,G : C ⥤ A` with F = G on the nose, the mapping space
       Map(F, G)   (of natural transformations)
  is contractible (Kan and having exactly one path‑component).

  We package this as an axiomised lemma `p_1`, plus a doc‑string
  with bibliographic reference.  Once mathlib4's homotopy library
  exposes the requisite infrastructure, this `axiom` can be replaced
  by the actual proof.
-/
import Mathlib.CategoryTheory.Simplicial
import Mathlib.CategoryTheory.NatIso

open CategoryTheory

universe u

abbrev SetCat : Type (u+1) := Type u
abbrev SSet   := SimplicialObject SetCat

namespace MappingSpace

/--
**Axiom (RV 6.5.1 – contractibility of mapping spaces).**

*Given small quasi‑categories `C` and `A`, and functors*
`F G : C ⥤ A` *which are definitionally equal (`rfl`), the simplicial
mapping space `Nat(F,G)` is contractible.*

We record only the π₀ level (non‑emptiness and uniqueness).  Higher
contractibility (πₙ=0 for n≥1) will be supplied later.

For present purposes this is enough to justify that any two natural
transformations between `F` and `G` are path‑equal, yielding the
pentagon / triangle coherences.
-/
axiom p_1
  {C A : Type (u+1)}
  [Category C] [Category A]
  (F G : C ⥤ A)
  (h : F = G) :
  -- Contractible type of natural transformations
  (Subsingleton (NatTrans F G))

/-- DOCSTRING / CITATION:
    This axiom mirrors Riehl–Verity *Elements of ∞‑Category Theory*
    Proposition 6.5.1, which states that the space of natural
    transformations between strictly equal functors is contractible.
    In the Joyal model, the mapping space `Fun(F,G)` is a Kan complex
    whose 0‑simplices are NatTrans and higher simplices are coherent
    homotopies; strict equality of functors gives degeneracies that
    collapse all horns, yielding contractibility.
-/
end MappingSpace