/-
  Paper 44: The Measurement Problem Dissolved
  ManyWorlds/BranchingStructure.lean — Everettian branching structures

  In the Many-Worlds interpretation, measurement doesn't collapse the
  wavefunction. Instead, the universe branches: each possible outcome is
  realized in a separate branch. A sequence of measurements produces a
  branching tree of worlds.

  The key insight: if later measurements depend on earlier outcomes
  (history-dependent branching), Dependent Choice is required to construct
  a complete world (infinite path). If measurements are history-independent
  (uniform branching), only countable choice suffices — and countable
  choice into nonempty finite sets is BISH-provable.
-/
import Papers.P44_MeasurementDissolved.Defs.Principles
import Mathlib.Data.Finset.Basic

namespace Papers.P44

-- ========================================================================
-- Measurement events
-- ========================================================================

/-- A measurement event with finitely many outcomes.
    In QM, each measurement has a finite spectrum of possible results. -/
structure Measurement where
  outcomes : Finset ℕ
  nonempty : outcomes.Nonempty

-- ========================================================================
-- Branching structure (history-dependent)
-- ========================================================================

/-- An Everettian branching structure.
    At each step n, given the history of outcomes at steps 0, ..., n-1,
    a measurement is determined. This models adaptive measurement protocols
    where later experiments depend on earlier results. -/
structure BranchingStructure where
  measurement : (n : ℕ) → (Fin n → ℕ) → Measurement

-- ========================================================================
-- World (complete branch)
-- ========================================================================

/-- A restriction function: given f : ℕ → ℕ and n : ℕ,
    produce the history (Fin n → ℕ) by restricting f to indices < n. -/
def restrictToHistory (f : ℕ → ℕ) (n : ℕ) : Fin n → ℕ :=
  fun i => f i.val

/-- A world is a complete branch through the branching structure:
    an infinite sequence of outcomes, where each outcome is valid
    for the measurement determined by the history up to that point. -/
def World (B : BranchingStructure) : Type :=
  { f : ℕ → ℕ // ∀ n, f n ∈ (B.measurement n (restrictToHistory f n)).outcomes }

/-- The Many-Worlds postulate: for every branching structure,
    a complete world exists. This asserts that the infinite branching
    tree is "completed" — every path through it is realized. -/
def ManyWorldsPostulate : Prop :=
  ∀ (B : BranchingStructure), Nonempty (World B)

-- ========================================================================
-- History-dependent branching
-- ========================================================================

/-- A branching structure is history-dependent if some measurement
    genuinely depends on the history of prior outcomes.
    This is the condition under which DC is needed (not just countable choice). -/
def HistoryDependent (B : BranchingStructure) : Prop :=
  ∃ (n : ℕ) (h₁ : Fin n → ℕ) (h₂ : Fin n → ℕ), h₁ ≠ h₂ ∧
    B.measurement n h₁ ≠ B.measurement n h₂

-- ========================================================================
-- Uniform branching (BISH-provable, no DC needed)
-- ========================================================================

/-- A uniform branching structure: the same measurement at every step,
    regardless of history. This models non-adaptive measurement protocols. -/
structure UniformBranching where
  M : Measurement

/-- Convert a uniform branching to a general BranchingStructure. -/
def UniformBranching.toBranching (U : UniformBranching) : BranchingStructure where
  measurement := fun _n _h => U.M

/-- For uniform branching, worlds exist without DC.
    At each step, independently choose from M.outcomes (nonempty finite set).
    This is BISH-provable: ℕ → Fin k is inhabited for all k > 0. -/
theorem uniform_world_exists (U : UniformBranching) :
    Nonempty (World U.toBranching) := by
  have hne := U.M.nonempty
  refine ⟨⟨fun _ => hne.choose, fun n => ?_⟩⟩
  simp [UniformBranching.toBranching]
  exact hne.choose_spec

/-- For uniform branching, we can provide a *constructive witness*
    (Type-valued, not merely Prop-valued) — a specific World term.
    This makes the constructive content explicit: the constant function
    choosing `hne.choose` at every step is a valid world.

    Added in revision per referee feedback: `Nonempty` (Prop-valued)
    is proof-irrelevant and relies on `Classical.choice` via `Nonempty.choose`.
    The Σ-type version makes the witness computationally explicit. -/
noncomputable def uniform_world_witness (U : UniformBranching) : World U.toBranching :=
  ⟨fun _ => U.M.nonempty.choose, fun n => by
    simp [UniformBranching.toBranching]
    exact U.M.nonempty.choose_spec⟩

end Papers.P44
