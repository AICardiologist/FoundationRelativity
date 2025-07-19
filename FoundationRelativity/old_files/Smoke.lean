/-
  Gap2.Smoke
  --------------------------------------------------------------------
  Quick checks for Gap₂ functor.
-/
import Gap2.Functor

open Foundation GapFunctor

/-- Identity on ZFC yields identity functor. -/
#eval (Gap2.map (Opposite.op Interp.id_zfc)).obj

/-- `incl` becomes functor `Gap(bish) → Gap(zfc)` (domain empty). -/
#eval (Gap2.map (Opposite.op Interp.incl))

/-- ρ-preview: explicit jump—empty in BISH, inhabited in ZFC (WLPO). -/
example : IsEmpty (GapWitness bish) := (gapEmpty).toIsEmpty
example : Nonempty (GapWitness zfc) := ⟨PUnit.unit⟩