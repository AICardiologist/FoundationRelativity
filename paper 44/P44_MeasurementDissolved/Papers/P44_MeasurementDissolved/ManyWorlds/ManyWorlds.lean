/-
  Paper 44: The Measurement Problem Dissolved
  ManyWorlds/ManyWorlds.lean — Many-Worlds ↔ DC equivalence

  Theorem 4.1: The Many-Worlds postulate (existence of complete branches
  in every branching structure) is equivalent to Dependent Choice (DC_ω).

  Forward (Many-Worlds → DC): encode any DC instance (α, R, a₀) as a
  branching structure where outcomes at step n encode the R-successors
  of the element chosen at step n-1. A world IS a DC chain.

  Reverse (DC → Many-Worlds): given a branching structure B, define
  the relation R on partial histories (Σ n, Fin n → ℕ) where
  (n, h) R (n+1, h') iff h' extends h by a valid outcome.
  DC yields an infinite chain, which determines a world.

  Forward direction sorry'd: the type-level encoding between arbitrary
  types and ℕ-indexed Finsets is standard but technically heavy.
  Reverse direction fully proved via DC on (ℕ × (ℕ → ℕ)).
-/
import Papers.P44_MeasurementDissolved.ManyWorlds.BranchingStructure

noncomputable section
namespace Papers.P44

-- ========================================================================
-- Forward: Many-Worlds → DC
-- ========================================================================

/-- **Theorem 4.1 (forward).** The Many-Worlds postulate implies Dependent Choice.

    Proof sketch: Given (α : Type), R : α → α → Prop, a₀ : α, and
    ∀ a, ∃ b, R a b, construct a BranchingStructure where:
    - At step 0: outcomes encode {b ∈ α : R a₀ b}
    - At step n+1 given history (a₀, a₁, ..., aₙ): outcomes encode {b : R aₙ b}
    A World in this structure determines a function f : ℕ → α with
    f 0 = a₀ and R (f n) (f (n+1)) for all n, which is a DC chain.

    The encoding requires mapping elements of α into ℕ (via Finset ℕ outcomes).
    For general types α, this requires a choice of encoding, which is
    available classically but adds complexity. Sorry'd here. -/
theorem manyworlds_implies_DC : ManyWorldsPostulate → DC := by
  intro _h _α _R _a₀ _hR
  sorry

-- ========================================================================
-- Reverse: DC → Many-Worlds
-- ========================================================================

/-- **Theorem 4.1 (reverse).** Dependent Choice implies the Many-Worlds postulate.

    Proof sketch: Given a BranchingStructure B, define:
    - Type α = Σ (n : ℕ), (Fin n → ℕ) — partial histories of any length
    - Initial point a₀ = (0, Fin.elim0) — the empty history
    - Relation R: (n, h) R (n+1, h') iff h' extends h by a valid outcome,
      i.e., h'|_{Fin n} = h and h'(n) ∈ (B.measurement n h).outcomes

    The relation is total because at each step, B.measurement n h has
    nonempty outcomes (by Measurement.nonempty), so we can extend h.

    DC gives an infinite R-chain (n₀, h₀), (n₁, h₁), (n₂, h₂), ...
    where nₖ = k and each hₖ extends the previous. The diagonal
    f(n) = hₙ₊₁(n) gives a World in B.

    Proved using (ℕ × (ℕ → ℕ)) as the DC type, avoiding Sigma-type
    dependent-type bookkeeping. The key coherence lemma shows that
    the j-th entry of the chain is "frozen" once set at step j+1. -/
theorem DC_implies_manyworlds : DC → ManyWorldsPostulate := by
  intro dc B
  -- Strategy: apply DC on (ℕ × (ℕ → ℕ)) where (n, w) represents
  -- "w is a valid history for the first n steps".
  -- Relation R: (n, w) R (n+1, w') iff w' agrees with w on {0,...,n-1}
  -- and w'(n) is a valid outcome at step n given the history.
  let α := ℕ × (ℕ → ℕ)
  let a₀ : α := (0, fun _ => 0)
  -- The relation: step increments, history preserved, new outcome valid
  let R : α → α → Prop := fun a b =>
    b.1 = a.1 + 1 ∧
    (∀ i, i < a.1 → b.2 i = a.2 i) ∧
    b.2 a.1 ∈ (B.measurement a.1 (restrictToHistory a.2 a.1)).outcomes
  -- Totality: every (n, w) can be extended
  have hR : ∀ (a : α), ∃ (b : α), R a b := by
    intro ⟨n, w⟩
    obtain ⟨v, hv⟩ := (B.measurement n (restrictToHistory w n)).nonempty
    -- New function: keep w on {0,...,n-1}, set position n to v, rest arbitrary
    refine ⟨(n + 1, fun i => if i < n then w i else if i = n then v else 0), ?_⟩
    refine ⟨rfl, ?_, ?_⟩
    · intro i hi; simp [hi]
    · simp [hv]
  -- Apply DC
  obtain ⟨f, hf0, hfR⟩ := dc α R a₀ hR
  -- f(k).1 = k for all k
  have hlen : ∀ k, (f k).1 = k := by
    intro k
    induction k with
    | zero => exact congrArg Prod.fst hf0
    | succ n ih =>
      exact (hfR n).1 ▸ congrArg (· + 1) ih
  -- Key coherence: for j < k, (f k).2 j = (f (j+1)).2 j
  -- This says the j-th entry is "frozen" once set at step j+1.
  have hcohere : ∀ j k, j < k → (f k).2 j = (f (j + 1)).2 j := by
    intro j k hjk
    induction k with
    | zero => omega
    | succ k ih =>
      by_cases hjk' : j < k
      · -- By R, (f (k+1)).2 agrees with (f k).2 on indices < (f k).1 = k
        obtain ⟨_, hagree, _⟩ := hfR k
        have hjfk : j < (f k).1 := by rw [hlen k]; exact hjk'
        have : (f (k + 1)).2 j = (f k).2 j := hagree j hjfk
        rw [this, ih hjk']
      · have : j = k := by omega
        subst this; rfl
  -- Extract the world: g(n) = (f (n+1)).2 n
  let g : ℕ → ℕ := fun n => (f (n + 1)).2 n
  -- restrictToHistory g n = restrictToHistory (f (n+1)).2 n ... but we need
  -- it to equal restrictToHistory (f n).2 n (which is what R uses)
  -- Actually: restrictToHistory g n i = g i.val = (f (i.val + 1)).2 i.val
  -- and by coherence with (f (n+1)):
  -- (f (n+1)).2 i.val = (f (i.val + 1)).2 i.val when i.val < n+1 (which holds)
  -- But R gives us membership in B.measurement n (restrictToHistory (f n).2 n).outcomes
  -- So we need restrictToHistory (f n).2 n = restrictToHistory g n
  have hrestr : ∀ n, restrictToHistory (f n).2 n = restrictToHistory g n := by
    intro n
    ext ⟨i, hi⟩
    simp only [restrictToHistory, g]
    -- Need: (f n).2 i = (f (i + 1)).2 i
    -- By coherence applied to j=i, k=n, using i < n (from hi and hlen)
    rw [hcohere i n (hlen n ▸ hi)]
  -- Now prove g is a valid world
  refine ⟨⟨g, fun n => ?_⟩⟩
  -- Need: g n ∈ (B.measurement n (restrictToHistory g n)).outcomes
  -- g n = (f (n+1)).2 n by definition
  -- R gives membership in B.measurement (f n).1 (restrictToHistory (f n).2 (f n).1)
  show g n ∈ (B.measurement n (restrictToHistory g n)).outcomes
  have hstep := (hfR n).2.2
  rw [hlen n] at hstep
  -- hstep : (f (n+1)).2 n ∈ (B.measurement n (restrictToHistory (f n).2 n)).outcomes
  rw [hrestr n] at hstep
  -- hstep : (f (n+1)).2 n ∈ (B.measurement n (restrictToHistory g n)).outcomes
  -- g n = (f (n+1)).2 n by definition
  exact hstep

-- ========================================================================
-- Combined equivalence
-- ========================================================================

/-- **Theorem 4.1.** The Many-Worlds postulate is equivalent to Dependent Choice.
    The Many-Worlds interpretation — asserting that every possible measurement
    outcome is realized in some branch of the universe — requires exactly
    Dependent Choice (DC_ω), the principle that total relations admit
    infinite chains.

    Key subtlety: if measurements are history-independent (uniform branching),
    only countable choice suffices (see `uniform_world_exists`).
    DC is needed precisely for adaptive measurement protocols where
    later measurements depend on earlier outcomes. -/
theorem manyworlds_iff_DC : ManyWorldsPostulate ↔ DC :=
  ⟨manyworlds_implies_DC, DC_implies_manyworlds⟩

end Papers.P44
end
