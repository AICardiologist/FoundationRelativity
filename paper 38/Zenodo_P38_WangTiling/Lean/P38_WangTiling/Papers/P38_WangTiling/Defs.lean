/-
  Paper 38: The Grandfather is LPO — Wang Tiling
  Defs.lean: Core definitions

  Wang tiles, tilesets, tiling predicates, aperiodicity,
  Turing machines, halting, LPO, and Σ₁⁰-completeness.
-/
import Mathlib.Topology.Order
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic

noncomputable section

-- ============================================================
-- Logical Principles
-- ============================================================

/-- LPO (Limited Principle of Omniscience). -/
def LPO : Prop :=
  ∀ (a : ℕ → Bool), (∀ n, a n = false) ∨ (∃ n, a n = true)

/-- WLPO (Weak LPO). -/
def WLPO : Prop :=
  ∀ (a : ℕ → Bool), (∀ n, a n = false) ∨ ¬(∀ n, a n = false)

/-- WLPO is subsumed by LPO. -/
theorem wlpo_of_lpo : LPO → WLPO := by
  intro hlpo a
  rcases hlpo a with h_all | ⟨n, hn⟩
  · left; exact h_all
  · right; intro h_all
    have := h_all n; rw [this] at hn; exact Bool.false_ne_true hn

-- ============================================================
-- Turing Machine Infrastructure
-- ============================================================

/-- Turing machines encoded as natural numbers. -/
def TM : Type := ℕ

/-- Halting indicator sequence (placeholder). -/
def halting_seq (_ : TM) : ℕ → Bool := fun _ => false

/-- A TM halts if its halting sequence has a true entry. -/
def halts (M : TM) : Prop := ∃ n, halting_seq M n = true

/-- Construct a TM from a binary sequence. -/
axiom tm_from_seq : (ℕ → Bool) → TM

/-- The constructed TM halts iff the sequence has a true entry. -/
axiom tm_from_seq_halts (a : ℕ → Bool) :
    halts (tm_from_seq a) ↔ ∃ n, a n = true

-- ============================================================
-- Wang Tile Definitions
-- ============================================================

/-- Colors for tile edges (abstract type). -/
def Color : Type := ℕ

/-- A Wang tile: four edge colors (top, bottom, left, right). -/
structure WangTile where
  top : Color
  bottom : Color
  left_color : Color
  right_color : Color

/-- A Wang tileset: a finite collection of Wang tiles.
    Represented as a list (finiteness is implicit). -/
abbrev WangTileset : Type := List WangTile

/-- A tiling assignment: each cell of ℤ² gets a WangTile. -/
def Tiling : Type := ℤ × ℤ → WangTile

/-- A tiling is valid if adjacent tiles share colors on common edges. -/
def valid_tiling (W : WangTileset) (T : Tiling) : Prop :=
  (∀ (i j : ℤ), T (i, j) ∈ W) ∧
  (∀ (i j : ℤ), (T (i, j)).right_color = (T (i+1, j)).left_color) ∧
  (∀ (i j : ℤ), (T (i, j)).top = (T (i, j+1)).bottom)

/-- A tileset tiles the plane if there exists a valid tiling. -/
def tiles_plane (W : WangTileset) : Prop :=
  ∃ (T : Tiling), valid_tiling W T

/-- A tiling is periodic if it has a non-zero translation period. -/
def periodic_tiling (T : Tiling) : Prop :=
  ∃ (px py : ℤ), (px ≠ 0 ∨ py ≠ 0) ∧
    ∀ (i j : ℤ), T (i, j) = T (i + px, j + py)

/-- A tileset tiles the plane aperiodically if it tiles the plane
    and every valid tiling is non-periodic. -/
def tiles_aperiodically (W : WangTileset) : Prop :=
  tiles_plane W ∧ ∀ (T : Tiling), valid_tiling W T → ¬periodic_tiling T

-- ============================================================
-- Σ₁⁰-Completeness
-- ============================================================

/-- A property P : TM → Prop is Σ₁⁰-complete if it is many-one
    equivalent to halting. -/
structure Sigma1Complete (P : TM → Prop) where
  /-- P reduces to halting. -/
  to_halting : ∀ (M : TM), P M → halts M
  /-- Halting reduces to P. -/
  from_halting : ∀ (M : TM), halts M → P M

-- ============================================================
-- Meta-theorem (imported from Paper 37 conceptually)
-- ============================================================

/-- The halting problem is undecidable. -/
axiom halting_problem_undecidable :
    ¬(∀ (M : TM), halts M ∨ ¬halts M)

/-- Meta-theorem: any halting-encoded property ≡ LPO.
    (Restated here for self-containedness; proved in Paper 37.) -/
theorem halting_reduction_iff_lpo
    {α : Type} (encode : (ℕ → Bool) → α)
    (P : α → Prop)
    (hP : ∀ (a : ℕ → Bool), P (encode a) ↔ ∃ n, a n = true) :
    (∀ (a : ℕ → Bool), P (encode a) ∨ ¬P (encode a)) ↔ LPO := by
  constructor
  · intro h_dec a
    rcases h_dec a with h_yes | h_no
    · right; exact (hP a).mp h_yes
    · left; intro n; by_contra h_ne
      have h_true : a n = true := by
        cases ha : a n with
        | false => exact absurd ha h_ne
        | true => rfl
      exact h_no ((hP a).mpr ⟨n, h_true⟩)
  · intro lpo a
    rcases lpo a with h_all | ⟨n, hn⟩
    · right; intro hP_yes
      have ⟨k, hk⟩ := (hP a).mp hP_yes
      have := h_all k; rw [this] at hk; exact Bool.false_ne_true hk
    · left; exact (hP a).mpr ⟨n, hn⟩

end
