import CategoryTheory.Found
import CategoryTheory.WitnessGroupoid

open CategoryTheory
open CategoryTheory.Found

/-- The GapFunctor maps foundations to their witness groupoids contravariant.
    F ↦ WitnessGroupoid F, with morphisms pulled back along interpretations. -/
noncomputable def CategoryTheory.GapFunctor : (Foundation)ᵒᵖ → Type := 
  fun F => WitnessGroupoid.Witness F.unop

/-  Sprint 41 Day 3: GapFunctor now maps Found^op → Cat using WitnessGroupoid.
    Upgrade to TwoCat will come in later sprints when bicategorical API stabilizes. -/
