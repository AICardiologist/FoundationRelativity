import Found.WitnessCore

open CategoryTheory Foundation Found

namespace APFail

/-- Type representing AP pathology -/
structure APPathology where
  data : Unit

/-- AP functor using the generic witness API -/
def AP_Fail₂ : Foundation ⥤ Cat := pathologyFunctor APPathology

end APFail