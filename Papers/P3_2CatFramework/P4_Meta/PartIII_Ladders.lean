/-
  Papers/P3_2CatFramework/P4_Meta/PartIII_Ladders.lean
  
  Part III ladders: LPO and iterated Con with concrete certificates.
  Provides toy ladder constructions with proven upper bounds.
-/
import Papers.P3_2CatFramework.P4_Meta.PartIII_Certificates
import Papers.P3_2CatFramework.P4_Meta.Meta_Signature

namespace Papers.P4Meta

/-! ### Arithmetical ladder (toy)
We model a "logical" ladder that adds `LPO` at step 0 and irrelevant fillers afterward.
-/

def LPO  : Formula := Formula.atom 310
def WLPO : Formula := Formula.atom 311

/-- Steps for the arith ladder: add `LPO` at step 0, dummy atoms thereafter. -/
def lArithSteps (T0 : Theory) : Nat → Formula
| 0     => LPO
| _     => Formula.atom 399   -- irrelevant filler

/-- Upper bound: at stage 1 (i.e. `Extend T0 LPO`) we have `LPO`. -/
theorem lpo_upper_one (T0 : Theory) :
  (ExtendIter T0 (lArithSteps T0) 1).Provable LPO := by
  -- stage 1 is `Extend T0 LPO`
  simpa [ExtendIter_succ, ExtendIter_zero, lArithSteps]
    using (Extend_Proves : (Extend T0 LPO).Provable LPO)

/-- Height certificate: `LPO` at height ≤ 1 along `lArithSteps`. -/
def lpo_height1_cert (T0 : Theory) :
  HeightCertificate T0 (lArithSteps T0) LPO :=
{ n := 1
, upper := lpo_upper_one T0
, note := "Upper: definitional. Lower: classical HA ⊬ LPO (provenance)."
}

/-! ### Consistency ladder (toy)
We model an "iterated consistency" ladder by adding a fresh token at each successor step.
-/

/-- Symbol for "Con at stage n" (just a fresh atom here). -/
def ConStep (n : Nat) : Formula := Formula.atom (330 + n)

/-- Steps for the consistency ladder: at step `n` add `ConStep n`. -/
def consSteps (S0 : Theory) : Nat → Formula
| n => ConStep n

/-- Upper bound: at stage `n+1` we can derive the token added at step `n`. -/
theorem cons_upper_succ (S0 : Theory) (n : Nat) :
  (ExtendIter S0 (consSteps S0) (n+1)).Provable (ConStep n) := by
  -- stage (n+1) is `Extend (stage n) (ConStep n)`
  simpa [ExtendIter_succ, consSteps]
    using (Extend_Proves :
      (Extend (ExtendIter S0 (consSteps S0) n) (ConStep n)).Provable (ConStep n))

/-- Height certificate: `ConStep n` at height ≤ `n+1`. -/
def con_height_cert (S0 : Theory) (n : Nat) :
  HeightCertificate S0 (consSteps S0) (ConStep n) :=
{ n := n + 1
, upper := cons_upper_succ S0 n
, note := s!"Upper: S_{n+1} ⊢ Con(S_n) (schematic); lower via classical G2 at each r.e. stage."
}

/-- The "filler" atom used in `lArithSteps` for steps ≥ 1. -/
def lpoFiller : Formula := Formula.atom 399

/-- Upper bound: at stage 2 we have the filler (added at step 1). -/
theorem lpo_filler_upper_two (T0 : Theory) :
  (ExtendIter T0 (lArithSteps T0) 2).Provable lpoFiller := by
  -- stage 2 = Extend (Extend T0 LPO) filler
  simpa [ExtendIter_succ, ExtendIter_zero, lArithSteps, lpoFiller]
    using (Extend_Proves :
      (Extend (Extend T0 LPO) lpoFiller).Provable lpoFiller)

/-- A height certificate for the filler at stage 2 (≤2). -/
def lpo_filler_height2_cert (T0 : Theory) :
  HeightCertificate T0 (lArithSteps T0) lpoFiller :=
{ n := 2
, upper := lpo_filler_upper_two T0
, note := "Upper: definitional (step 1 is filler), hence height ≤ 2."
}

end Papers.P4Meta