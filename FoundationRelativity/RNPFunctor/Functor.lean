import Found.WitnessCore

open CategoryTheory Foundation Found

namespace RNPFail

/-- Type representing RNP pathology -/
structure RNPPathology where
  data : Unit

/-- RNP functor using the generic witness API -/
def RNP_Fail₂ : Foundation ⥤ Cat := pathologyFunctor RNPPathology

end RNPFail