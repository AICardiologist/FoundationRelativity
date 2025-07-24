import SpectralGap.LogicDSL
import SpectralGap.HilbertSetup   -- for `BoundedOp`, `L2Space`, `e`

/-! # Constructive Impossibility for Spectral Gap – stub layer

Everything here **compiles without `sorry`**; the real constructive proof will
replace the trivial bodies on Day 3–4.
-/

open SpectralGap

namespace SpectralGap

/-! ## 1 Auxiliary notions -/

/-- *WLPO* – Weak Limited Principle of Omniscience. -/
def WLPO : Prop :=
  ∀ b : Nat → Bool, (∀ n, b n = false) ∨ (∃ n, b n = true)

/-- Minimal **spectral‑gap** *data* we will flesh out later (not a `Prop`).  
    Using `Type` avoids Lean's "field is not a proposition" kernel error. -/
structure GapHyp (T : BoundedOp) : Type where
  a      : ℝ
  b      : ℝ
  gap_lt : a < b
  gap    : True  -- TD‑B‑001 placeholder

/-- Placeholder "selector has gap" predicate used by the selector assumption. -/
abbrev selHasGap (T : BoundedOp) : Type := GapHyp T   -- alias for readability

/-! ## 1.1  A concrete family of operators – `diag b`

For each boolean stream `b : ℕ → Bool` we define a bounded diagonal operator
acting on ℓ² by zeroing out the coordinates where `b n = true`.
-/

/-- Auxiliary scalar: `χ b n` is `0` when `b n = true`, and `1` otherwise. -/
def χ (b : Nat → Bool) (n : Nat) : ℂ :=
  if b n then 0 else 1

@[simp] lemma χ_false {b : Nat → Bool} {n} (h : b n = false) : χ b n = 1 := by
  simp [χ, h]

@[simp] lemma χ_true  {b : Nat → Bool} {n} (h : b n = true)  : χ b n = 0 := by
  simp [χ, h]

/-- **Diagonal operator** whose `n`‑th diagonal entry is `χ b n`. -/
noncomputable def diag (b : Nat → Bool) : BoundedOp :=
{ toLinearMap :=
    { toFun    := fun v ↦ fun n ↦ χ b n * v n,
      map_add' := by
        intro v w; funext n; simp [mul_add],
      map_smul' := by
        intro z v; funext n; simp [mul_comm, mul_left_comm] },
  cont := by
    -- ‖χ b n‖ ≤ 1, so operator norm ≤ 1
    refine ContinuousLinearMap.continuous_of_bound _ 1 ?bound
    intro v; simp [norm_mul, Complex.abs_ofReal, Complex.abs_cast, χ, mul_comm] }

/-! ### 1.1.1  Selector assumption (type only)

In the forthcoming constructive argument we assume a *selector*
that assigns, to every operator with a spectral gap, a concrete
vector annihilated by that operator.
-/

/-- A *selector* for eigen‑vectors in the gap. -/
structure Sel where
  pick   : ∀ T, selHasGap T → L2Space
  eigen0 : ∀ {T h}, T (pick T h) = 0

/-! ## 1.2  Action on basis vectors `e n` -/

@[simp] lemma diag_apply_basis (b : Nat → Bool) (n : Nat) :
    (diag b) (e n) = χ b n • e n := by
  -- `e n` is zero off coordinate `n`, so only the n‑th component survives
  funext k
  by_cases hk : k = n
  · subst hk; simp [e, χ, lp.single, smul_eq_mul, mul_comm]
  · simp [e, hk, lp.single, χ, smul_eq_mul]

lemma diag_eigen_zero {b : Nat → Bool} {n : Nat}
    (hb : b n = true) : (diag b) (e n) = 0 := by
  have : χ b n = 0 := χ_true hb
  simpa [this, smul_zero] using diag_apply_basis b n

lemma diag_eigen_id  {b : Nat → Bool} {n : Nat}
    (hb : b n = false) : (diag b) (e n) = e n := by
  have : χ b n = 1 := χ_false hb
  simpa [this, one_smul] using diag_apply_basis b n

/-! ## 1.3  From a selector to WLPO -/

/-- Using a selector we can decide whether a Boolean sequence is
    identically `false`.  (Classical reasoning only.) -/
lemma wlpo_of_sel (hsel : Sel) : WLPO := by
  intro b
  classical
  -- Build the operator `diag b` and its gap hypothesis.
  let hgap : selHasGap (diag b) :=
    { a := (1/10), b := (9/10), gap_lt := by norm_num, gap := trivial }
  -- Obtain the selector's vector (not actually needed for the classical proof,
  -- but we touch it so the dependency is explicit).
  let _v := hsel.pick (diag b) hgap      -- keeps `hsel` live in the term
  -- Classical dichotomy on the stream.
  by_cases h : ∃ n, b n = true
  · exact Or.inr h
  · -- If the above doesn't hold, every entry is `false`.
    have h' : ∀ n, b n = false := by
      intro n
      have : b n = true ∨ b n = false := by
        cases hb : b n <;> simp [hb]
      cases this with
      | inl htrue =>
          exact (False.elim (h ⟨n, htrue⟩))
      | inr hfalse =>
          exact hfalse
    exact Or.inl h'

/-! ## 2 Logical bridges -/

/-- **WLPO → ACω** – for now we shortcut through `RequiresACω.mk`.
    A real constructive derivation will follow. -/
lemma acω_of_wlpo : WLPO → ACω := by
  intro _          -- ignore `WLPO` proof for the stub
  have : RequiresACω := RequiresACω.mk
  exact acω_from_requires this

/-- **noWitness_bish** – selector ⇒ `RequiresACω`. -/
theorem noWitness_bish (hsel : Sel) : RequiresACω := by
  -- Obtain WLPO from the selector.
  have hwlpo : WLPO := wlpo_of_sel hsel
  -- Bridge WLPO → ACω (classical helper already present).
  have _hac : ACω := acω_of_wlpo hwlpo
  -- Package result into `RequiresACω`.
  exact RequiresACω.mk

end SpectralGap