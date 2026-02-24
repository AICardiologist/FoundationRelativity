/-
Papers/P25_ChoiceAxis/Basic.lean
Paper 25: Choice-Axis Calibration in Mathematical Physics

Core definitions of choice principles (CC, DC, AC₀) and their hierarchy.
These are the logical principles calibrated against physical theories in
this paper.

The choice hierarchy: AC₀ < CC < DC < Full AC.
  - AC₀ (finite choice): trivially provable in BISH
  - CC  (countable choice): calibrates to mean ergodic / weak LLN
  - DC  (dependent choice): calibrates to Birkhoff pointwise / strong LLN
  - Full AC: produces only mathematical pathologies (Vitali, Banach-Tarski)
-/
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fin.Basic

namespace Papers.P25_ChoiceAxis

/-! ## Choice Principles -/

/-- **Countable Choice (CC_ℕ)**: Given a sequence of nonempty subsets of ℕ,
    there exists a choice function selecting an element from each set.

    This is the standard constructive formulation (Bishop-style) restricted
    to subsets of ℕ. It is equivalent to the general CC for complete
    separable metric spaces. -/
def CC_N : Prop :=
  ∀ (A : ℕ → Set ℕ), (∀ n, (A n).Nonempty) → ∃ f : ℕ → ℕ, ∀ n, f n ∈ A n

/-- **Countable Choice (sequence form)**: Given P : ℕ → ℕ → Prop with
    ∀ n, ∃ m, P n m, there exists a choice function f with ∀ n, P n (f n).

    Logically equivalent to CC_N. This form is more convenient for
    the ergodic theorem encoding. -/
def CC_seq : Prop :=
  ∀ (P : ℕ → ℕ → Prop), (∀ n, ∃ m, P n m) → ∃ f : ℕ → ℕ, ∀ n, P n (f n)

/-- **Dependent Choice (DC)**: Given a total binary relation R on a type X,
    and an initial element x₀, there exists an infinite sequence threading
    through R starting from x₀.

    DC is strictly stronger than CC: it allows each choice to depend on
    the outcome of the previous choice.

    Standard formulation (Bridges-Vita 2006). -/
def DC : Prop :=
  ∀ (X : Type) (R : X → X → Prop),
    (∀ x, ∃ y, R x y) → ∀ x₀ : X, ∃ f : ℕ → X, f 0 = x₀ ∧ ∀ n, R (f n) (f (n + 1))

/-- **Finite Choice (AC₀)**: Choice from a finite family of nonempty types.
    Trivially provable in BISH via induction — no genuine choice principle. -/
def AC0 : Prop :=
  ∀ (k : ℕ) (A : Fin k → Set ℕ), (∀ i, (A i).Nonempty) → ∃ f : Fin k → ℕ, ∀ i, f i ∈ A i

/-! ## Equivalence of CC formulations -/

/-- CC_N and CC_seq are logically equivalent. -/
theorem cc_n_iff_cc_seq : CC_N ↔ CC_seq := by
  constructor
  · intro hcc P hP
    have : ∀ n, ({m : ℕ | P n m}).Nonempty := by
      intro n; obtain ⟨m, hm⟩ := hP n; exact ⟨m, hm⟩
    obtain ⟨f, hf⟩ := hcc (fun n => {m | P n m}) this
    exact ⟨f, hf⟩
  · intro hcc A hA
    have : ∀ n, ∃ m, m ∈ A n := by
      intro n; exact hA n
    obtain ⟨f, hf⟩ := hcc (fun n m => m ∈ A n) this
    exact ⟨f, hf⟩

/-! ## Choice Hierarchy: DC → CC → AC₀ -/

/-- **DC implies CC_N.** Standard result in constructive mathematics.

    Proof: Given nonempty sets A(n), define X = ℕ × ℕ with relation
    R (n, a) (n', a') iff n' = n + 1 ∧ a' ∈ A(n'). DC gives a thread;
    projecting out the second components yields a choice function. -/
theorem cc_n_of_dc : DC → CC_N := by
  intro hdc A hA
  -- Use DC on X = ℕ × ℕ with R encoding "next index, valid choice"
  have htotal : ∀ (p : ℕ × ℕ), ∃ q : ℕ × ℕ, q.1 = p.1 + 1 ∧ q.2 ∈ A q.1 := by
    intro ⟨n, _⟩
    obtain ⟨m, hm⟩ := hA (n + 1)
    exact ⟨(n + 1, m), rfl, hm⟩
  -- Get initial element from A 0
  obtain ⟨a₀, ha₀⟩ := hA 0
  -- Apply DC with relation "next step is valid"
  obtain ⟨f, hf0, hstep⟩ := hdc (ℕ × ℕ) (fun p q => q.1 = p.1 + 1 ∧ q.2 ∈ A q.1)
    (fun p => htotal p) (0, a₀)
  -- The choice function is n ↦ (f n).2
  -- First show (f n).1 = n by induction
  have hfst : ∀ n, (f n).1 = n := by
    intro n
    induction n with
    | zero => simp [hf0]
    | succ k ih =>
      have := (hstep k).1
      omega
  -- Now extract the choice function
  refine ⟨fun n => (f n).2, fun n => ?_⟩
  cases n with
  | zero => simp [hf0]; exact ha₀
  | succ k =>
    have := (hstep k).2
    rwa [hfst (k + 1)] at this

/-- **CC_N implies AC₀.** Countable choice subsumes finite choice,
    since Fin k embeds into ℕ. -/
theorem ac0_of_cc_n : CC_N → AC0 := by
  intro hcc k A hA
  -- Extend the finite family to a countable one
  let A' : ℕ → Set ℕ := fun n =>
    if h : n < k then A ⟨n, h⟩ else {0}
  have hA' : ∀ n, (A' n).Nonempty := by
    intro n
    simp only [A']
    split
    · exact hA _
    · exact ⟨0, rfl⟩
  obtain ⟨f, hf⟩ := hcc A' hA'
  refine ⟨fun i => f i.val, fun i => ?_⟩
  have := hf i.val
  simp only [A', dif_pos i.isLt] at this
  exact this

/-- **DC implies AC₀** (transitive). -/
theorem ac0_of_dc : DC → AC0 := fun hdc => ac0_of_cc_n (cc_n_of_dc hdc)

end Papers.P25_ChoiceAxis
