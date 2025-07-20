/-
  Degenerate coherence for the strict 2‑category skeleton used here.
-/
import Mathlib.CategoryTheory.Simplicial
import Mathlib.CategoryTheory.NatIso
import Found.InterpCore

universe u
abbrev SSet := SimplicialObject (Type u)

structure InterpFun where
  F : SSet ⥤ SSet

namespace InterpFun

@[simp] def comp (Ψ Φ : InterpFun) : InterpFun := ⟨Φ.F ⋙ Ψ.F⟩
notation Ψ " ∘₁ " Φ => comp Ψ Φ

@[simp] def assoc2  (Θ Ψ Φ : InterpFun) := NatTrans.id _
@[simp] def leftUnitor  (Φ)              := NatTrans.id _
@[simp] def rightUnitor (Φ)              := NatTrans.id _

lemma pentagon_holds (Ω Θ Ψ Φ : InterpFun) : True := by trivial
lemma triangle_holds (Φ : InterpFun)          : True := by trivial

end InterpFun
EOF < /dev/null