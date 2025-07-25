import Gap2.Functor
import Found.LogicDSL
import Found.WitnessCore

open CategoryTheory Foundation Found Gap

namespace Gap.Proofs

/-- The constructive (bish) witness type for Gap₂ is empty. -/
theorem noWitness_bish : IsEmpty (WitnessType Gap₂Pathology bish) := by
  -- by definition WitnessType … bish = Empty
  simp [WitnessType]
  exact inferInstance

/-- The classical (zfc) witness type for Gap₂ is inhabited (has ⟨⟩). -/
theorem witness_zfc : Nonempty (WitnessType Gap₂Pathology zfc) := by
  -- WitnessType … zfc = PUnit, which is inhabited by ⟨()⟩
  simp [WitnessType]
  exact ⟨PUnit.unit⟩

/-- Gap₂ pathology therefore **requires WLPO** in order to obtain a witness. -/
theorem Gap_requires_WLPO : RequiresWLPO (Nonempty (WitnessType Gap₂Pathology zfc)) :=
  Found.RequiresWLPO.intro witness_zfc

end Gap.Proofs