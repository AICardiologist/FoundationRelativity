import Papers.P3C_DCwAxis.DCw_Frontier_Interface

/-!
# Paper 3C: DCω → Baire Proof Skeleton

Complete mathematical proof (0 sorries) building chains via DCω and diagonal limits,
without dependency on topology libraries.
-/


namespace Papers.P3C.DCw

abbrev Seq := Nat → Nat

structure Cyl where
  stem : List Nat
deriving Repr, Inhabited

/-- A sequence lies in a cylinder if it agrees with its stem on all positions. -/
def Cyl.mem (C : Cyl) (x : Seq) : Prop :=
  ∀ i : Fin C.stem.length, x i = C.stem.get i

namespace Cyl
  /-- Extend a cylinder by one symbol. -/
  def extend (C : Cyl) (a : Nat) : Cyl := ⟨C.stem ++ [a]⟩

  @[simp] theorem extend_stem (C : Cyl) (a : Nat) :
      (C.extend a).stem = C.stem ++ [a] := rfl

  @[simp] theorem extend_length (C : Cyl) (a : Nat) :
      (C.extend a).stem.length = C.stem.length + 1 := by simp

end Cyl

/-- Dense-open placeholder on cylinders (to be replaced by topology later). -/
structure DenseOpen where
  hit    : Cyl → Prop
  dense  : ∀ C : Cyl, ∃ C' : Cyl, C'.stem.length ≥ C.stem.length ∧ hit C'
  /-- One-step openness: from any cylinder, some one-symbol extension hits. -/
  refine1 : ∀ C : Cyl, ∃ a : Nat, hit (Cyl.extend C a)

/-- Stage-indexed refinement: at stage `n`, extend by one symbol and meet `U n`. -/
def stepRAt (U : Nat → DenseOpen) (n : Nat) (C C' : Cyl) : Prop :=
  ∃ a, C'.stem = C.stem ++ [a] ∧ (U n).hit C'

/-- "F is an indexed chain": the (n+1)-th cylinder refines the n-th meeting `U n`. -/
def isChainAt (U : Nat → DenseOpen) (F : Nat → Cyl) : Prop :=
  ∀ n, stepRAt U n (F n) (F (n+1))

/-- For each stage `n` and cylinder `C`, refine by one symbol hitting `U n`. -/
theorem step_exists (U : Nat → DenseOpen) :
  ∀ (C : Cyl) (n : Nat), ∃ (C' : Cyl), ∃ a : Nat,
    C'.stem = C.stem ++ [a] ∧ (U n).hit C' := by
  intro C n
  rcases (U n).refine1 C with ⟨a, h⟩
  refine ⟨Cyl.extend C a, a, ?_, h⟩
  simp  -- uses Cyl.extend_stem

/-- DCω state for the construction: stage counter paired with a cylinder. -/
structure State where
  n : Nat
  C : Cyl

/-- The DCω relation: `(n,C) → (n+1,C')` forcing `stepRAt U n C C'`. -/
def R (U : Nat → DenseOpen) (s s' : State) : Prop :=
  s'.n = s.n + 1 ∧ stepRAt U s.n s.C s'.C

/-- Totality of `R` from any state, delegated to `step_exists`. -/
theorem R_total (U : Nat → DenseOpen) :
  ∀ s : State, ∃ s' : State, R U s s' := by
  intro s
  rcases step_exists U s.C s.n with ⟨C', a, hEq, hHit⟩
  exact ⟨⟨s.n + 1, C'⟩, ⟨rfl, ⟨a, hEq, hHit⟩⟩⟩

/-- Build an infinite indexed chain of refinements via DCω. -/
theorem chain_of_DCω (hDC : DCω) (U : Nat → DenseOpen) (C0 : Cyl) :
  ∃ F : Nat → Cyl, F 0 = C0 ∧ isChainAt U F := by
  -- Apply DCω to the state machine
  obtain ⟨f, hf0, hfstep⟩ := hDC (R U) (R_total U) ⟨0, C0⟩
  -- Extract the cylinder sequence
  let F : Nat → Cyl := fun n => (f n).C
  refine ⟨F, ?_, ?_⟩
  · -- Show F 0 = C0
    simp [F, hf0]
  · -- Show isChainAt U F
    intro n
    -- We need to show stepRAt U n (F n) (F (n+1))
    simp only [F]
    -- Goal: stepRAt U n (f n).C (f (n+1)).C
    -- We have hfstep n : R U (f n) (f (n + 1))
    have hR := hfstep n
    -- By definition of R, we get:
    -- hR.1: (f (n+1)).n = (f n).n + 1
    -- hR.2: stepRAt U (f n).n (f n).C (f (n+1)).C
    -- We need to show (f n).n = n
    have hn : (f n).n = n := by
      clear hR
      induction n with
      | zero => simp [hf0]
      | succ k ih =>
        have hRk := hfstep k
        calc (f (k + 1)).n = (f k).n + 1 := hRk.1
          _ = k + 1 := by rw [ih]
    -- Now we can conclude
    -- hR says: R U (f n) (f (n + 1))
    -- target: stepRAt U n (F n) (F (n+1))
    simpa [F, R, hn] using hR.2


-- Helper lemmas for finishing the proof later

theorem step_length_succ {U : Nat → DenseOpen} {n : Nat} {C C' : Cyl} :
  stepRAt U n C C' → C'.stem.length = C.stem.length + 1 := by
  intro h; rcases h with ⟨a, hEq, _⟩; simp [hEq]

theorem step_prefix {C C' : Cyl} {a : Nat} :
  C'.stem = C.stem ++ [a] → C'.stem.take C.stem.length = C.stem := by
  intro h; simp [h]

@[simp] theorem mem_nil (x : Seq) : (⟨[]⟩ : Cyl).mem x := by
  intro i; exact Fin.elim0 i

/-- Single-step refinement relation. -/
def refines1 (C C' : Cyl) : Prop := ∃ a, C'.stem = C.stem ++ [a]

@[simp] theorem refines1_length {C C'} :
  refines1 C C' → C'.stem.length = C.stem.length + 1 := by
  intro h; rcases h with ⟨a, hEq⟩; simp [hEq]

theorem chain_refines1 {U F} (h : isChainAt U F) :
  ∀ n, refines1 (F n) (F (n+1)) := by
  intro n; rcases h n with ⟨a, hEq, _⟩; exact ⟨a, hEq⟩

/-! ### Length monotonicity and suffix decomposition along a chain -/

-- Lengths are monotone along the chain.
theorem length_mono_of_chain {U} {F : Nat → Cyl} (h : isChainAt U F)
    {m n : Nat} (hmn : m ≤ n) : (F m).stem.length ≤ (F n).stem.length := by
  induction hmn with
  | refl => exact Nat.le_refl _
  | @step k _ ih =>
    have hstep : (F (k+1)).stem.length = (F k).stem.length + 1 :=
      step_length_succ (h k)
    calc (F m).stem.length
      ≤ (F k).stem.length := ih
      _ ≤ (F (k+1)).stem.length := by rw [hstep]; exact Nat.le_succ _

-- Every later stem is an earlier stem followed by a suffix.
theorem stems_suffix {U} {F : Nat → Cyl} (h : isChainAt U F)
    {m n : Nat} (hmn : m ≤ n) : ∃ s : List Nat, (F n).stem = (F m).stem ++ s := by
  induction hmn with
  | refl => exact ⟨[], by simp⟩
  | @step k _ ih =>
    rcases ih with ⟨s, hs⟩
    rcases h k with ⟨a, hEq, _⟩
    refine ⟨s ++ [a], ?_⟩
    simp [hs, hEq, List.append_assoc]

/-- From the empty cylinder, lengths are exactly the stage index. -/
@[simp] theorem len_from_nil {U} {F} (h0 : F 0 = ⟨[]⟩) (h : isChainAt U F) (n : Nat) :
    (F n).stem.length = n := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    have := step_length_succ (h n)
    simp [ih] at this ⊢
    exact this

/-- Prefix stability along the chain: earlier stems are prefixes of later stems. -/
theorem prefix_between {U} {F : Nat → Cyl} (h : isChainAt U F)
    {m n : Nat} (hmn : m ≤ n) :
    (F n).stem.take (F m).stem.length = (F m).stem := by
  classical
  rcases stems_suffix h hmn with ⟨s, hs⟩
  simp [hs]

/-! ### Small utilities for `get` on appended/prefixed lists -/

-- If `l₂ = l₁ ++ s` and `i < length l₁`, then the `i`-th entry of `l₂` equals the `i`-th of `l₁`.
theorem get_of_prefix {α} {l₁ l₂ s : List α} {i : Nat}
    (h : l₂ = l₁ ++ s) (hi : i < l₁.length) :
    l₂.get ⟨i, by
      rw [h, List.length_append]
      exact Nat.lt_add_right _ hi⟩
  = l₁.get ⟨i, hi⟩ := by
  simp [h, List.getElem_append_left hi]

-- The boundary case for a singleton suffix.
@[simp] theorem get_boundary_append_singleton {α} (l : List α) (a : α) :
    (l ++ [a]).get ⟨l.length, by simp⟩ = a := by
  -- `simp` knows how to reduce this via `List.get_append_right`
  simp

noncomputable section
open Classical

/-- Read the "digit added at step i" from the chain. -/
noncomputable def digit {U} {F : Nat → Cyl} (h : isChainAt U F) (i : Nat) : Nat :=
  Classical.choose (chain_refines1 h i)

theorem digit_spec {U} {F} (h : isChainAt U F) (i : Nat) :
  (F (i+1)).stem = (F i).stem ++ [digit h i] := by
  dsimp [digit]
  exact Classical.choose_spec (chain_refines1 h i)

/-- Define the actual limit using digits (one new symbol per step). -/
noncomputable def limit_of_chain (U) {F} (h : isChainAt U F) : Seq :=
  fun i => digit h i

end

/-- The limit realizes every finite stem in the chain. -/
theorem limit_mem (U : Nat → DenseOpen) {F : Nat → Cyl}
    (h0 : F 0 = ⟨[]⟩) (hchain : isChainAt U F) :
    ∀ n, (F n).mem (limit_of_chain U hchain) := by
  classical
  -- Induction on n
  refine Nat.rec ?base ?step
  · -- n = 0: empty stem, no indices
    intro i
    -- rewrite the index type to `Fin 0` and eliminate
    rw [h0] at i
    exact Fin.elim0 i
  · -- step: assume for n, prove for n+1
    intro n IH i
    -- Standard length facts
    have hlen_n    : (F n).stem.length     = n     := len_from_nil h0 hchain n
    have hlen_succ : (F (n+1)).stem.length = n + 1 := len_from_nil h0 hchain (n+1)
    -- One-step refinement description
    rcases hchain n with ⟨a, hEq, _⟩
    have happ : (F (n+1)).stem = (F n).stem ++ [a] := by simp [hEq]
    -- Compare `i` with the old length `n`
    have ile : i.val ≤ n := by
      have h1 : i.val < (F (n+1)).stem.length := i.isLt
      have h2 : (F (n+1)).stem.length = n + 1 := hlen_succ
      have h3 : i.val < n + 1 := by rw [← h2]; exact h1
      exact Nat.le_of_lt_succ h3
    rcases Nat.lt_or_eq_of_le ile with hlt | heq
    · -- Case 1: i.val < n, so we read from the left block (F n).stem
      have hi : i.val < (F n).stem.length := by rw [hlen_n]; exact hlt
      -- Under the append equality, the i-th element is the same as in (F n).stem
      have hi_succ : i.val < (F (n+1)).stem.length := i.isLt
      have eq_get :
          (F (n+1)).stem.get ⟨i.val, hi_succ⟩
            = (F n).stem.get ⟨i.val, hi⟩ := by
        -- read from the left part when `i.val < (F n).stem.length`
        simp [happ, List.getElem_append_left hi]
      -- Evaluate the limit at the old stage using the IH, then transport along `eq_get`
      have : (limit_of_chain U hchain) i
          = (F n).stem.get ⟨i.val, hi⟩ := by
        -- the sequence is `Nat → Nat`, so `i` is used via its `val`
        change (limit_of_chain U hchain) i.val = (F n).stem.get ⟨i.val, hi⟩
        exact IH ⟨i.val, hi⟩
      -- Turn RHS into what we need at stage n+1
      rw [this, eq_get]
    · -- Case 2: i.val = n, so we read the newly appended digit
      -- The "digit" chosen at stage `n` describes `(F (n+1)).stem` as `append` with singleton
      have step_eq :
          (F (n+1)).stem = (F n).stem ++ [digit hchain n] :=
        digit_spec hchain n
      -- The last entry of `l ++ [a]` is exactly `a`
      have hn_bound : n < (F (n+1)).stem.length := by
        rw [hlen_succ]; exact Nat.lt_succ_self n
      have boundary :
          (F (n+1)).stem.get ⟨n, hn_bound⟩
            = digit hchain n := by
        have hlen : (F n).stem.length = n := hlen_n
        simp [step_eq, hlen]
      -- Replace the index `i` by the canonical boundary index (proof-irrelevant)
      have hi_eq : i = ⟨n, hn_bound⟩ := by
        apply Fin.ext
        simp [heq]
      -- Convert `boundary` to the index `i`
      have boundary_i : (F (n+1)).stem.get i = digit hchain n := by
        rw [hi_eq]
        exact boundary
      -- The diagonal limit at index `i` is exactly that digit
      -- (rewrite `i.val` to `n` via `heq`)
      simp [limit_of_chain, heq, boundary_i.symm]

end Papers.P3C.DCw