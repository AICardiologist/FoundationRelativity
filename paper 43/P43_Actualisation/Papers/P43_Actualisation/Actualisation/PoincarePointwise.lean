/-
  Paper 43: What the Ceiling Means
  Actualisation/PoincarePointwise.lean — Poincaré recurrence actualisation

  "This specific orbit returns to A" requires:
    Step 1 (BISH): μ(never-return set) = 0  [Theorem 3]
    Step 2 (Cournot): ω ∉ never-return set
    Step 3 (MP): ¬(∀k>0, f^k(ω) ∉ A) → ∃k>0, f^k(ω) ∈ A

  Same logical structure as radioactive decay.
  Unlike decay, there is no computable return time (the return time
  depends on Diophantine properties of the orbit). Yet the logical
  cost is the same: Cournot + MP.
-/
import Papers.P43_Actualisation.Defs.Cournot
import Papers.P43_Actualisation.BISHContent.PoincareMeasure
import Papers.P43_Actualisation.Hierarchy.LPOImpliesMP

namespace Papers.P43

open MeasureTheory Function

-- ========================================================================
-- Step 2 (Cournot): This point is not in the non-returning set
-- ========================================================================

/-- Cournot: a specific point ω ∈ A is not in the non-returning set.
    Since μ(neverReturn f A) = 0 (Theorem 3), Cournot excludes ω from it. -/
theorem not_never_return
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ]
    {f : α → α} (hf : MeasurePreserving f μ μ)
    {A : Set α} (hA : NullMeasurableSet A μ)
    (ω : α) (hω : ω ∈ A) :
    ¬(∀ k, 0 < k → f^[k] ω ∉ A) := by
  intro h_never
  exact cournot (poincare_nonreturn_measure_zero hf hA) ω ⟨hω, h_never⟩

-- ========================================================================
-- Step 3 (MP): This orbit eventually returns to A
-- ========================================================================

/-- Actualisation: this orbit eventually returns to A.
    Requires: MP + Cournot + BISH (Poincaré recurrence).

    The `mem_dec` oracle provides a decidable membership test,
    required to encode the problem as a binary sequence for MP. -/
theorem orbit_returns_mp
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ]
    {f : α → α} (hf : MeasurePreserving f μ μ)
    {A : Set α} (hA : NullMeasurableSet A μ)
    (hMP : MarkovPrinciple)
    (mem_dec : α → ℕ → Bool)
    (h_equiv : ∀ (x : α) (k : ℕ), f^[k] x ∈ A ↔ mem_dec x k = true)
    (ω : α) (hω : ω ∈ A) :
    ∃ k, 0 < k ∧ f^[k] ω ∈ A := by
  -- Define shifted binary sequence: α_seq(n) = mem_dec ω (n+1)
  -- so α_seq(n) = true ↔ f^[n+1] ω ∈ A
  let α_seq : ℕ → Bool := fun n => mem_dec ω (n + 1)
  -- From Cournot: ¬(∀ k > 0, f^[k] ω ∉ A)
  have h_not_all : ¬(∀ n, α_seq n = false) := by
    intro h_all_false
    apply not_never_return hf hA ω hω
    intro k hk
    rw [h_equiv]
    simp only [Bool.not_eq_true]
    -- k > 0 means k = (k-1) + 1 for some k-1
    have hk' : k = (k - 1) + 1 := by omega
    rw [hk']
    exact h_all_false (k - 1)
  -- Apply MP to get ∃n, α_seq(n) = true
  obtain ⟨n, hn⟩ := hMP α_seq h_not_all
  -- Translate back: f^[n+1] ω ∈ A
  exact ⟨n + 1, Nat.succ_pos n, (h_equiv ω (n + 1)).mpr hn⟩

end Papers.P43
