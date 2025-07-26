/-!
# The 2‑Category `Found` – sprint‑40 skeleton
#
# Objects   : `Foundation` – an opaque type for now.
# 1‑morphisms: `Interp`    – data of an interpretation (functor part only).
# 2‑morphisms: `Interp₂`   – natural transformation between functor parts.
#
# This version is *strict* and proof‑minimal.  It compiles, so the rest of the
# repo will accept `import CategoryTheory.Found`.  Coherence fillers will be
# added in the day‑5 task.
-/

import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

/-‐-----------------------------------------------------------------/
/- Objects -/
/-‐-----------------------------------------------------------------/

/-- A "foundation" is currently just a tag; the analytic details live elsewhere. -/
opaque Foundation : Type

/-- Skeleton category of foundations -/
instance : Category Foundation where
  Hom      := fun _ _ ↦ Unit        -- placeholder for `Interp`
  id       := fun _   ↦ ()
  comp     := fun _ _ _ _ _ ↦ ()

/-- 1‑morphisms (interpretations) – *placeholder* -/
abbrev Interp (F₁ F₂ : Foundation) := PUnit

/-- 2‑morphisms between interpretations – also placeholder -/
abbrev Interp₂ {F₁ F₂ : Foundation} (Φ Ψ : Interp F₁ F₂) := Unit

/-‐-----------------------------------------------------------------/
/- Namespace packaging -/
/-‐-----------------------------------------------------------------/

namespace CategoryTheory.Found

abbrev Obj := Foundation

end CategoryTheory.Found