import CategoryTheory.Found

open CategoryTheory

/-- **Stub**: contravariant 2-functor that will collect gap witnesses.
    Filled in Sprint 41. -/
noncomputable
def CategoryTheory.GapFunctor : Opposite Found → Type _ := by
  -- TODO(S41): upgrade to `Opposite Found ⥤ TwoCat` after Unicode issue fixed
  exact fun _ ↦ PUnit

/-  Keeping this file separate means downstream imports already compile. -/