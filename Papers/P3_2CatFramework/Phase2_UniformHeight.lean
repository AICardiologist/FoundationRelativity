import Mathlib.Logic.Equiv.Basic
import Papers.P3_2CatFramework.Phase1_Simple

/-!
  # Phase 2: Uniformization Height Theory Core

  Core scaffolding for uniformization at the Σ₀ (pinned) layer.
  
  ## Contents
  - Σ₀ signature elements as indices
  - Witness families indexed by foundations and Σ₀
  - Uniformization functors on subcategories
  - Main theorem: bidual gap has height = 1
  
  This module depends only on Phase1_Simple.lean (toy bicategory).
-/

open Papers.P3.Phase1Simple

namespace Papers.P3.Phase2

/-! ------------------------------------------------------------
    Σ₀ : pinned signature as *indices* (names only)
    ------------------------------------------------------------ -/

/-- 
Σ₀ signature elements (pinned across all foundations).

These are the fixed mathematical objects that exist in all foundations:
- Basic types: nat, bool, real
- Sequence spaces: ℓ∞ (bounded sequences), c₀ (null sequences)
- Quotient map: ℓ∞ → ℓ∞/c₀
-/
inductive Sigma0
  | nat
  | bool
  | real
  | ellInf      -- ℓ∞
  | c0          -- c₀
  | quo_linf_c0 -- ℓ∞ ⟶ ℓ∞/c₀ (we only need the *name* at Phase 2)
deriving DecidableEq, Repr

/-- 
Truth value as a type (Bishop's approach).

- `Truth true` = PUnit (inhabited)
- `Truth false` = Empty (uninhabited)

Used for encoding logical conditions as type inhabitation.
-/
def Truth (b : Bool) : Type := if b then PUnit else Empty

lemma Truth_true  : Truth true  = PUnit := rfl
lemma Truth_false : Truth false = Empty  := rfl

-- Helper equivalences to avoid dependent rewrite issues
-- produce an equivalence Truth b ≃ PUnit when b = true, by case-splitting the equality
private def truthEquivPUnit_of_true {b : Bool} (hb : b = true) : Truth b ≃ PUnit :=
by cases hb; exact Equiv.refl _

-- and the inverse PUnit ≃ Truth b
private def punitEquivTruth_of_true {b : Bool} (hb : b = true) : PUnit ≃ Truth b :=
(truthEquivPUnit_of_true hb).symm

/-! ------------------------------------------------------------
    Foundations, levels, and the WLPO bit
    ------------------------------------------------------------ -/

-- We **reuse** the Phase 1 `Foundation` and example objects.
abbrev Foundation := Papers.P3.Phase1Simple.Foundation
abbrev Interp     := Papers.P3.Phase1Simple.Interp

-- Examples from Phase 1:
abbrev BISH        : Foundation := Papers.P3.Phase1Simple.BISH
abbrev BISH_WLPO   : Foundation := Papers.P3.Phase1Simple.BISH_WLPO
abbrev inclusionBW : Interp BISH BISH_WLPO := Papers.P3.Phase1Simple.bish_to_wlpo

/-- 
Extract the WLPO status from a foundation.

Returns true if the foundation includes the Weak Limited Principle of Omniscience.
-/
@[simp]
def hasWLPO (F : Foundation) : Bool := F.wlpo

@[simp] lemma hasWLPO_BISH     : hasWLPO BISH = false := rfl
@[simp] lemma hasWLPO_BISH_WLPO : hasWLPO BISH_WLPO = true := rfl

/-- 
Foundations at height ≥ 0 (all foundations).
-/
@[simp]
def W_ge0 : Foundation → Prop := fun _ => True

/-- 
Foundations at height ≥ 1 (those with WLPO).
-/
@[simp]
def W_ge1 : Foundation → Prop := fun F => hasWLPO F = true

/-! ------------------------------------------------------------
    Witness families and uniformization at Σ₀
    ------------------------------------------------------------ -/

/-- 
A witness family indexed by foundations and Σ₀ elements.

Assigns to each foundation F and Σ₀ element X a type C(F,X) of witnesses.
The size field tracks complexity (e.g., number of parameters).
-/
structure WitnessFamily where
  C : Foundation → Sigma0 → Type

/-- Uniformization-on-a-sub-2-category, but *only at Σ₀*.
    
    This structure is restricted to Σ₀ components (pinned objects) and encodes 
    only the equivalences there, not full pseudofunctor data. For each 
    interpretation Φ inside W, we package an equivalence at every pinned X : Σ₀,
    with identity and composition laws at Σ₀.
    
    Note: This is intentionally limited in scope - we only track witness 
    equivalences at the pinned signature objects, not at arbitrary Banach spaces.
-/
structure UniformizableOn (W : Foundation → Prop) (WF : WitnessFamily) where
  η :
    ∀ {F F'} (_ : Interp F F'), W F → W F' →
      ∀ X : Sigma0, (WF.C F X) ≃ (WF.C F' X)
  η_id :
    ∀ {F} (hF : W F) X,
      η (id_interp F) hF hF X = Equiv.refl (WF.C F X)
  η_comp :
    ∀ {F G H} (φ : Interp F G) (ψ : Interp G H)
      (hF : W F) (hG : W G) (hH : W H) X,
      η (comp_interp φ ψ) hF hH X
        = (η φ hF hG X).trans (η ψ hG hH X)

/-! ------------------------------------------------------------
    Case study: the bidual gap as a witness family
    ------------------------------------------------------------ -/

/-- Gap witness family at Σ₀. By design:
    - at X = ℓ∞ we reflect the WLPO bit (Empty vs PUnit),
    - at other Σ₀ objects we return a trivial singleton (irrelevant here).
    This encodes the "truth groupoid" for the gap at pinned objects.
-/
def GapFamily : WitnessFamily where
  C F X :=
    match X with
    | Sigma0.ellInf      => Truth (hasWLPO F)  -- "empty ↔¬ WLPO, singleton ↔ WLPO"
    | _                  => PUnit

@[simp] lemma GapFamily_at_ellInf (F : Foundation) :
  GapFamily.C F Sigma0.ellInf = Truth (hasWLPO F) := rfl

@[simp] lemma GapFamily_at_other (F : Foundation) (X)
  (hX : X ≠ Sigma0.ellInf) :
  GapFamily.C F X = PUnit := by
  cases X <;> simp [GapFamily]
  case ellInf => contradiction

/-! ------------------------------------------------------------
    Height = 1: non-uniformizable at ≥0; uniformizable at ≥1
    ------------------------------------------------------------ -/

/-- No uniformization at height 0 (contains BISH ↪ BISH+WLPO). -/
theorem no_uniformization_height0 :
  ¬ (Nonempty (UniformizableOn W_ge0 GapFamily)) := by
  intro h
  rcases h with ⟨U⟩
  -- Consider Φ : BISH ⟶ BISH+WLPO at X = ℓ∞.
  have e := U.η inclusionBW (trivial) (trivial) Sigma0.ellInf
  -- Evaluate both sides.
  -- Left: Truth (hasWLPO BISH) = Empty
  -- Right: Truth (hasWLPO BISH+WLPO) = PUnit
  have e' : Truth (hasWLPO BISH) ≃ Truth (hasWLPO BISH_WLPO) := e
  -- Convert to `Empty ≃ PUnit`.
  have : Empty ≃ PUnit := by
    simpa [Truth, hasWLPO_BISH, hasWLPO_BISH_WLPO] using e'
  -- Impossible: extract an element of `Empty`.
  exact (by cases this.symm ⟨⟩)

/-- Uniformization at height 1: on any pair of foundations with WLPO,
    the gap-truth at ℓ∞ is constantly `PUnit`, so the identity equivalence suffices. -/
def uniformization_height1 : UniformizableOn W_ge1 GapFamily :=
{ η := fun {F F'} _ (hF : W_ge1 F) (hF' : W_ge1 F') X =>
    match X with
    | Sigma0.nat      => Equiv.refl _
    | Sigma0.bool     => Equiv.refl _
    | Sigma0.real     => Equiv.refl _
    | Sigma0.c0       => Equiv.refl _
    | Sigma0.quo_linf_c0 => Equiv.refl _
    | Sigma0.ellInf =>
        -- At height ≥1, hasWLPO F = true and hasWLPO F' = true
        -- So Truth (hasWLPO F) = PUnit and Truth (hasWLPO F') = PUnit
        -- We need Truth (hasWLPO F) ≃ Truth (hasWLPO F')
        -- Since both equal PUnit, use the helper functions
        (truthEquivPUnit_of_true hF).trans (punitEquivTruth_of_true hF')
, η_id := fun {F} (hF : W_ge1 F) X => by
    cases X
    case nat | bool | real | c0 | quo_linf_c0 => rfl
    case ellInf =>
      -- At ellInf, we need to show the η equivalence equals Equiv.refl
      simp only [GapFamily]
      -- The equivalence is (truthEquivPUnit_of_true hF).trans (punitEquivTruth_of_true hF)
      -- This is Truth (hasWLPO F) → PUnit → Truth (hasWLPO F), which should be identity
      -- Since these are inverses by construction
      ext x
      simp only [Equiv.trans_apply, Equiv.refl_apply]
      -- Use the fact that composing with inverse gives identity
      have : (punitEquivTruth_of_true hF) ((truthEquivPUnit_of_true hF) x) = x := by
        -- This is true because punitEquivTruth_of_true is the inverse of truthEquivPUnit_of_true
        simp only [punitEquivTruth_of_true, truthEquivPUnit_of_true, Equiv.symm_apply_apply]
      exact this
, η_comp := fun {F G H} φ ψ (hF : W_ge1 F) (hG : W_ge1 G) (hH : W_ge1 H) X => by
    cases X
    case nat | bool | real | c0 | quo_linf_c0 => rfl
    case ellInf =>
      simp only [GapFamily]
      -- Need to show η(comp φ ψ) = trans (η φ) (η ψ)
      -- All equivalences at height ≥1 are between PUnit types
      ext x
      -- All the compositions work out because we're just composing PUnit equivalences
      rfl }

/-- Corollary packaging the "height = 1" statement. -/
theorem gap_height_eq_one :
  (¬ Nonempty (UniformizableOn W_ge0 GapFamily))
  ∧ Nonempty (UniformizableOn W_ge1 GapFamily) :=
⟨no_uniformization_height0, ⟨uniformization_height1⟩⟩

/-! Small smoke tests you can keep or remove. -/
#check gap_height_eq_one
#check uniformization_height1
#check no_uniformization_height0

/-! ------------------------------------------------------------
    Σ₀-pseudofunctor + natural transformations (thin version)
    ------------------------------------------------------------ -/

/-- A Σ₀-pseudofunctor skeleton: acts on pinned objects only. -/
structure Sigma0Pseudo where
  C    : Foundation → Sigma0 → Type
  map  : ∀ {F F'} (_ : Interp F F'), (X : Sigma0) → C F X → C F' X
  map_id  :
    ∀ {F} X, map (id_interp F) X = id
  map_comp :
    ∀ {F G H} (φ : Interp F G) (ψ : Interp G H) X,
      map (comp_interp φ ψ) X = (map ψ X) ∘ (map φ X)

/-- A Σ₀-natural transformation between Σ₀-pseudofunctors. -/
structure Sigma0NatTrans (P Q : Sigma0Pseudo) where
  app : ∀ F X, P.C F X → Q.C F X
  naturality :
    ∀ {F F'} (Φ : Interp F F') X (x : P.C F X),
      app F' X (P.map Φ X x) = Q.map Φ X (app F X x)

end Papers.P3.Phase2