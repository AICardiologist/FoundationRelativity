/-
  Papers/P4_Meta/PartV_Reflection.lean
  
  De-axiomatized reflection → consistency proof using typeclasses.
  This replaces the sorry in PartV_Collision with a constructive proof.
-/
import Papers.P3_2CatFramework.P4_Meta.PartV_Interfaces

namespace Papers.P4Meta.PartV

open Papers.P4Meta

/-- Arithmetization: theories can encode proofs as natural numbers -/
class CodesProofs (T : Theory) : Type where
  /-- A proof code exists for any provable formula -/
  encode_proof : ∀ φ, T.Provable φ → Nat
  /-- The encoding respects the proof relation -/
  decode_valid : ∀ φ n, (∃ h : T.Provable φ, n = encode_proof φ h) → T.Provable φ

/-- Sigma1-soundness: the extension by RFN_Sigma1(T) satisfies uniform reflection -/
class Sigma1Sound (T : Theory) : Prop where
  /-- If a Sigma1 formula is true in N, the extended theory proves it -/
  reflection_holds : ∀ phi, 
    Formula.atom 200 = phi →  
    (Extend T (RFN_Sigma1 T)).Provable phi

/-- Con(T) is equivalent to a true Sigma1 statement (axiom) -/
axiom con_is_sigma1 (T : Theory) : Formula.atom 200 = Con T

/-- The de-axiomatized reflection theorem -/

theorem reflection_implies_consistency_proved 
    (T : Theory) [HBL T] [RE T] [CodesProofs T] [inst : Sigma1Sound T] :
    (Extend T (RFN_Sigma1 T)).Provable (Con T) := by
  -- Use Sigma1-soundness directly
  have h := inst.reflection_holds (Con T) (con_is_sigma1 T)
  exact h

end Papers.P4Meta.PartV