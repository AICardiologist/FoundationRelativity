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

/-- Minimal **spectral‑gap** record we will flesh out later.  For now it simply
    carries the numerical bounds `0.1 < 0.9`. -/
structure GapHyp (T : BoundedOp) : Prop where
  a       : ℝ := 0.1
  b       : ℝ := 0.9
  gap_lt  : a < b                := by norm_num
  gap     : True                 -- TD‑B‑001 placeholder

/-- Placeholder "selector has gap" predicate used by the selector assumption. -/
abbrev selHasGap (T : BoundedOp) : Prop := GapHyp T   -- alias for readability

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

notation "T[" b "]" => diag b

/-! ## 1.2  Action on basis vectors `e n` -/

@[simp] lemma diag_apply_basis (b : Nat → Bool) (n : Nat) :
    T[b] (e n) = χ b n • e n := by
  -- `e n` is zero off coordinate `n`, so only the n‑th component survives
  funext k
  by_cases hk : k = n
  · subst hk; simp [e, χ, lp.single, smul_eq_mul, mul_comm]
  · simp [e, hk, lp.single, χ, smul_eq_mul]

lemma diag_eigen_zero {b : Nat → Bool} {n : Nat}
    (hb : b n = true) : T[b] (e n) = 0 := by
  have : χ b n = 0 := χ_true hb
  simpa [this, smul_zero] using diag_apply_basis b n

lemma diag_eigen_id  {b : Nat → Bool} {n : Nat}
    (hb : b n = false) : T[b] (e n) = e n := by
  have : χ b n = 1 := χ_false hb
  simpa [this, one_smul] using diag_apply_basis b n

/-! ## 2 Logical bridges -/

/-- **WLPO → ACω** – for now we shortcut through `RequiresACω.mk`.
    A real constructive derivation will follow. -/
lemma acω_of_wlpo : WLPO → ACω := by
  intro _          -- ignore `WLPO` proof for the stub
  have : RequiresACω := RequiresACω.mk
  exact acω_from_requires this

/-- **noWitness_bish (stub)**  
    If a *selector* exists that produces an eigen‑vector in the gap of *every*
    operator, we obtain `RequiresACω`.  Currently a trivial proof; tomorrow we
    replace it with the WLPO reduction. -/
theorem noWitness_bish
    (hsel : ∃ sel : (∀ T : BoundedOp, selHasGap T → L2Space),
              True) : RequiresACω := by
  exact RequiresACω.mk

end SpectralGap