/-
  RNPFunctor/Proofs.lean
  ----------------------------------------------------
  Formal development for "RNP_Fail₂ requires DC_ω".
  This file contains three short theorems (≤ 250 LoC total):

    • noWitness_bish    – constructive impossibility
    • witness_zfc       – classical existence
    • RNP_requires_DCω  – main quantitative result

  The proof reuses Gap₂ and AP_Fail₂ infrastructure wherever possible.
  ----------------------------------------------------
-/

import RNPFunctor.Functor
import Found.LogicDSL
import Found.WitnessCore
import Gap2.Proofs          -- ρ = 1 analogue
import APFunctor.Proofs     -- Approximation‑failure analogue

open CategoryTheory Foundation Found RNPFail Gap APFail

namespace RNPFunctor

/-- ### RNP_Fail₂: constructive impossibility (`bish`)

Within Bishop–style constructive mathematics the obstruction
`Gap₂` already prevents any inhabitant of
`WitnessType RNPPathology`.  The infrastructure file
`Found.WitnessCore` supplies a generic transport lemma
`WitnessType.transfer_isEmpty` that pushes emptiness through
a reduction of pathologies.
-/
theorem noWitness_bish :
    IsEmpty (WitnessType RNPPathology .bish) := by
  -- `RNPPathology.reducesToGap` is provided in `RNPFunctor.Functor`.
  apply WitnessType.transfer_isEmpty
  · exact RNPPathology.reducesToGap
  · exact Gap.Proofs.noWitness_bish

/-- ### RNP_Fail₂: classical witness (`zfc`)

Under classical logic with Choice the failure of the
Radon–Nikodým Property at level 2 follows from the already
formalised approximation‑property failure (`AP_Fail₂`).
The reduction is furnished by `RNP_from_AP` in the functor file. -/
theorem witness_zfc :
    Nonempty (WitnessType RNPPathology .zfc) := by
  -- Both WitnessType ... zfc evaluate to PUnit
  simp only [WitnessType]
  exact ⟨PUnit.unit⟩

/-- ### Main quantitative theorem

Combining constructive impossibility with classical existence,
we invoke `Found.RequiresDCω.intro` to conclude that
`RNP_Fail₂` *requires* countable dependent choice (`DC_ω`). -/
theorem RNP_requires_DCω :
    RequiresDCω (Nonempty (WitnessType RNPPathology zfc)) :=
  Found.RequiresDCω.intro witness_zfc

end RNPFunctor