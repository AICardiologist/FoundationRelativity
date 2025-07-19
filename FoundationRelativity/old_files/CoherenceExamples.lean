import Found.Coherence
import Found.Interpretation
open Interp

universe u

/-- Concrete interpretation coming from Set ↦ SSet ↦ Set trick. -/
def Φ : Interp := iota_cl_interp

lemma four_comp_id : (Φ ∘₁ Φ ∘₁ Φ ∘₁ Φ).F = Φ.F := rfl

#eval (Φ ∘₁ Φ ∘₁ Φ ∘₁ Φ).F   -- prints the underlying functor, confirming equality

/-- Associator/unitors are still identities for Φ. -/
example : assoc2 Φ Φ Φ = NatTrans.id _ := rfl
example : leftUnitor Φ               = NatTrans.id _ := rfl
example : rightUnitor Φ              = NatTrans.id _ := rfl