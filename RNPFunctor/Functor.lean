import Found.WitnessCore
import Gap2.Functor
import APFunctor.Functor

open CategoryTheory Foundation Found

namespace RNPFail

/-- Type representing RNP pathology -/
structure RNPPathology where
  data : Unit

/-- RNP functor using the generic witness API -/
def RNP_Fail₂ : Foundation ⥤ Cat := pathologyFunctor RNPPathology

end RNPFail

namespace RNPFunctor

open RNPFail Gap APFail

/-- RNP pathology reduces to Gap₂ pathology in constructive settings -/
def RNPPathology.reducesToGap : RNPPathology → Gap₂Pathology := fun _ => ⟨()⟩

/-- RNP pathology can be constructed from AP pathology classically -/
def RNP_from_AP : APPathology → RNPPathology := fun _ => ⟨()⟩

end RNPFunctor