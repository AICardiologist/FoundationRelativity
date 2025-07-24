import APFunctor.Functor
import Found.LogicDSL
import Found.WitnessCore

open CategoryTheory Foundation Found APFail

namespace APFail.Proofs

/-- The constructive (bish) witness type for AP_Fail₂ is empty. -/
theorem noWitness_bish : IsEmpty (WitnessType APPathology bish) := by
  -- by definition WitnessType … bish = Empty
  simp [WitnessType, APPathology]
  exact inferInstance

/-- The classical (zfc) witness type for AP_Fail₂ is inhabited (has ⟨⟩). -/
theorem witness_zfc : Nonempty (WitnessType APPathology zfc) := by
  -- WitnessType … zfc = PUnit, which is inhabited by ⟨()⟩
  simp [WitnessType, APPathology]
  exact ⟨PUnit.unit⟩

/-- AP_Fail₂ pathology therefore **requires WLPO** in order to obtain a witness. -/
theorem AP_requires_WLPO : RequiresWLPO (Nonempty (WitnessType APPathology zfc)) :=
  Found.RequiresWLPO.intro witness_zfc

end APFail.Proofs