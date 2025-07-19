import Found.WitnessCore

open CategoryTheory Foundation Found

namespace Gap

/-- Type representing Gap₂ pathology -/
structure Gap₂Pathology where
  data : Unit

/-- Gap₂ functor using the generic witness API -/
def Gap₂ : Foundation ⥤ Cat := pathologyFunctor Gap₂Pathology

end Gap