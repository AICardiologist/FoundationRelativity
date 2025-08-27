/-
  File: Papers/P3_2CatFramework/P4_Meta/Frontier_API.lean
  
  A tiny "portal" API: shuttle reductions across a fixed equivalence (WLPO ↔ Gap).
  This is deliberately minimal and proof-irrelevant (Prop-only).
  
  Purpose:
  - Provide compositional bridges for moving calibrations through WLPO ↔ Gap
  - Enable one-line conversions from WLPO-facing to Gap-facing theorems
  - Support height certificate transport across equivalences
-/
namespace Papers.P4Meta

/-- A one-way reduction `P → Q`. -/
structure ReducesTo (P Q : Prop) : Prop where
  run : P → Q

-- Scoped infix for readability:  P ⟶ Q  means  ReducesTo P Q
scoped infixr:55 " ⟶ " => ReducesTo

/-- Build a reduction from a plain function `P → Q`. -/
@[inline] def reduces {P Q : Prop} (f : P → Q) : P ⟶ Q := ⟨f⟩

/-- Reductions from an equivalence: left-to-right and right-to-left. -/
@[inline] def reduces_of_iff_mp {P Q : Prop} (e : P ↔ Q) : P ⟶ Q := ⟨e.mp⟩
@[inline] def reduces_of_iff_mpr {P Q : Prop} (e : P ↔ Q) : Q ⟶ P := ⟨e.mpr⟩

/-- Compose one-way reductions. -/
def ReducesTo.trans {P Q R : Prop} (f : ReducesTo P Q) (g : ReducesTo Q R) : ReducesTo P R :=
  ⟨fun p => g.run (f.run p)⟩

/-- Compose reductions with `calc` via the standard `Trans` typeclass. -/
instance : Trans ReducesTo ReducesTo ReducesTo where
  trans := ReducesTo.trans

/-- Run view. Handy if you need to extract the function behind a reduction. -/
@[simp] theorem ReducesTo.run_trans {P Q R} (f : P ⟶ Q) (g : Q ⟶ R) :
    (ReducesTo.trans f g).run = fun p => g.run (f.run p) := rfl

/-- Shuttle a reduction `P → B` through an equivalence `A ↔ B` to get `P → A`. -/
def toLeft {A B P : Prop} (E : A ↔ B) (f : ReducesTo P B) : ReducesTo P A :=
  ⟨fun p => E.mpr (f.run p)⟩

/-- Shuttle a reduction `P → A` through an equivalence `A ↔ B` to get `P → B`. -/
def toRight {A B P : Prop} (E : A ↔ B) (f : ReducesTo P A) : ReducesTo P B :=
  ⟨fun p => E.mp (f.run p)⟩

/-- If we have `P → B` and `B → P`, then, via `A ↔ B`, we get `P ↔ A`. -/
theorem iff_through {A B P : Prop} (E : A ↔ B)
    (f : ReducesTo P B) (g : ReducesTo B P) : P ↔ A :=
  Iff.intro
    (fun p => E.mpr (f.run p))
    (fun a => g.run (E.mp a))

/-! ### Specializations: the WLPO ↔ Gap portal -/

/-- Turn `P → WLPO` into `P → Gap` using `Gap ↔ WLPO`. -/
def toGap_of_toWLPO {WLPO Gap P : Prop} (portal : Gap ↔ WLPO)
    (f : ReducesTo P WLPO) : ReducesTo P Gap :=
  toLeft portal f

/-- Turn `P → Gap` into `P → WLPO` using `Gap ↔ WLPO`. -/
def toWLPO_of_toGap {WLPO Gap P : Prop} (portal : Gap ↔ WLPO)
    (f : ReducesTo P Gap) : ReducesTo P WLPO :=
  toRight portal f

/-- If `P` reduces to WLPO and WLPO reduces to `P`, then `P ↔ Gap`. -/
theorem equiv_with_Gap_via_WLPO {WLPO Gap P : Prop} (portal : Gap ↔ WLPO)
    (toW : ReducesTo P WLPO) (fromW : ReducesTo WLPO P) : P ↔ Gap :=
  let pEquivW : P ↔ WLPO := iff_through (Iff.rfl) toW fromW
  pEquivW.trans portal.symm

/-- Convenience lambda-view wrappers. -/
theorem toGap_of_toWLPO' {WLPO Gap P : Prop} (portal : Gap ↔ WLPO)
    (f : P → WLPO) : P → Gap :=
  fun p => portal.mpr (f p)

theorem toWLPO_of_toGap' {WLPO Gap P : Prop} (portal : Gap ↔ WLPO)
    (f : P → Gap) : P → WLPO :=
  fun p => portal.mp (f p)

theorem equiv_with_Gap_via_WLPO' {WLPO Gap P : Prop} (portal : Gap ↔ WLPO)
    (toW : P → WLPO) (fromW : WLPO → P) : P ↔ Gap :=
  Iff.intro (fun p => portal.mpr (toW p)) (fun g => fromW (portal.mp g))

/-! ### Height transport template 

  Template signatures (adapt to your real Height/Certificate API):
  We assume: (1) height is monotone under implication,
              (2) height is invariant under equivalence,
              (3) Gap has a known height certificate.
-/
section HeightTransport

-- These are template variables - replace with actual Height API
variable {HeightCert : Prop → Prop}
variable {Gap WLPO : Prop}

theorem height_of_from_WLPO 
    (height_mono : ∀ {P Q}, (P → Q) → HeightCert P → HeightCert Q)
    (portal : Gap ↔ WLPO)
    (gap_h1 : HeightCert Gap)
    {P : Prop}
    (fromW : WLPO → P) : HeightCert P :=
  -- Gap → P via Gap → WLPO (portal.mp), then WLPO → P (fromW)
  height_mono (fun (g : Gap) => fromW (portal.mp g)) gap_h1

theorem height_of_equiv_with_Gap 
    (height_equiv : ∀ {P Q}, (P ↔ Q) → HeightCert Q → HeightCert P)
    (gap_h1 : HeightCert Gap)
    {P : Prop}
    (e : P ↔ Gap) : HeightCert P :=
  height_equiv e gap_h1

end HeightTransport

/-! ### Example: Stone calibration hook

  Example wiring for Stone-style statements without heavy dependencies.
  This shows how any calibrator can immediately leverage the portal.
-/
section StoneExample

variable (WLPO Gap SurjDZ : Prop)
variable (portal : Gap ↔ WLPO)
variable (surjDZ_to_WLPO : SurjDZ → WLPO)
variable (WLPO_to_surjDZ : WLPO → SurjDZ)

/-- Suppose (to be proven in your Stone section) that SurjDZ ⇒ WLPO.
    Then SurjDZ ⇒ Gap follows by a single portal step. -/
def surjDZ_to_Gap : SurjDZ → Gap :=
  fun s => portal.mpr (surjDZ_to_WLPO s)

/-- If you also show WLPO ⇒ SurjDZ, you get SurjDZ ↔ Gap immediately. -/
def surjDZ_equiv_Gap : SurjDZ ↔ Gap :=
  Iff.intro 
    (fun s => portal.mpr (surjDZ_to_WLPO s))
    (fun g => WLPO_to_surjDZ (portal.mp g))

end StoneExample

/-! ### Generic height lifting helper -/

/-- Generic height lift along an implication. -/
@[inline] def height_lift_of_imp
    {HeightCert : Prop → Prop}
    (height_mono : ∀ {P Q}, (P → Q) → HeightCert P → HeightCert Q)
    {P Q : Prop} (hP : HeightCert P) (imp : P → Q) : HeightCert Q :=
  height_mono imp hP

end Papers.P4Meta