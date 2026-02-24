/-
  Paper 58: Class Number Correction — Norm Obstruction
  Norm representability proofs for K = ℚ(√-5).

  Key results:
    - Mod-5 descent: for f ≡ 2,3 mod 5, f is not a rational norm in ℚ(√-5)×
    - Explicit norm witnesses for free and non-free cases
    - Steinitz class forced by norm obstruction
    - Inert conductor classification
-/
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Int.Basic

/-!
# Norm Obstruction

A positive rational r lies in Nm(ℚ(√-5)×) iff r = a² + 5b² for some a, b ∈ ℚ,
equivalently: ∃ x y z : ℤ, z ≠ 0 ∧ x² + 5y² = r · z².

The mod-5 descent argument shows that for f ≡ 2 or 3 mod 5, the equation
x² + 5y² = f · z² has no integer solution with z ≠ 0.
-/

-- ========================================================================
-- Section 1: Mod-5 descent (general)
-- ========================================================================

/-- In ZMod 5, the only squares are {0, 1, 4}.
    Neither 2 nor 3 is a product of two squares in ZMod 5. -/
private lemma zmod5_no_sq_eq_2_mul_sq :
    ∀ (a b : ZMod 5), b ≠ 0 → a ^ 2 ≠ 2 * b ^ 2 := by decide

private lemma zmod5_no_sq_eq_3_mul_sq :
    ∀ (a b : ZMod 5), b ≠ 0 → a ^ 2 ≠ 3 * b ^ 2 := by decide

/-- Helper: cast f % 5 = 2 to (f : ZMod 5) = 2. -/
private lemma intCast_zmod5_of_mod_eq_2 {f : ℤ} (hf : f % 5 = 2) :
    (f : ZMod 5) = 2 := by
  have : ((f - 2 : ℤ) : ZMod 5) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; omega
  have h : (f : ZMod 5) - 2 = 0 := by push_cast at this; exact this
  exact sub_eq_zero.mp h

/-- Helper: cast f % 5 = 3 to (f : ZMod 5) = 3. -/
private lemma intCast_zmod5_of_mod_eq_3 {f : ℤ} (hf : f % 5 = 3) :
    (f : ZMod 5) = 3 := by
  have : ((f - 3 : ℤ) : ZMod 5) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; omega
  have h : (f : ZMod 5) - 3 = 0 := by push_cast at this; exact this
  exact sub_eq_zero.mp h

/-- 5 is prime in ℤ. -/
private lemma int_prime_five : Prime (5 : ℤ) := by
  rw [Int.prime_iff_natAbs_prime]; norm_num

/-- Auxiliary: if x² + 5y² = f·z² with f ≡ 2,3 mod 5, then 5 ∣ z.
    Proof: in ZMod 5, x² = f·z² (since 5y² ≡ 0). If z ≢ 0 mod 5,
    then z is a unit, so f = (x/z)² is a square mod 5. But 2,3 are not. -/
private theorem div5_of_norm_eq {f x y z : ℤ}
    (hf : f % 5 = 2 ∨ f % 5 = 3)
    (heq : x ^ 2 + 5 * y ^ 2 = f * z ^ 2) :
    (5 : ℤ) ∣ z := by
  by_contra h5z
  -- Cast to ZMod 5
  have hcast : (x : ZMod 5) ^ 2 + 5 * (y : ZMod 5) ^ 2 =
      (f : ZMod 5) * (z : ZMod 5) ^ 2 := by
    have := congr_arg (Int.cast : ℤ → ZMod 5) heq
    push_cast at this
    exact this
  have h5_zero : (5 : ZMod 5) = 0 := by decide
  simp [h5_zero] at hcast
  -- z ≠ 0 in ZMod 5
  have hz_ne : (z : ZMod 5) ≠ 0 := by
    intro hz
    apply h5z
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  -- f mod 5 in ZMod 5
  rcases hf with hf2 | hf3
  · rw [intCast_zmod5_of_mod_eq_2 hf2] at hcast
    exact absurd hcast (zmod5_no_sq_eq_2_mul_sq _ _ hz_ne)
  · rw [intCast_zmod5_of_mod_eq_3 hf3] at hcast
    exact absurd hcast (zmod5_no_sq_eq_3_mul_sq _ _ hz_ne)

/-- If x² + 5y² = f·z² and 5 | z, then 5 | x. -/
private theorem div5_x_of_div5_z {f x y z : ℤ}
    (heq : x ^ 2 + 5 * y ^ 2 = f * z ^ 2)
    (hz : (5 : ℤ) ∣ z) : (5 : ℤ) ∣ x := by
  obtain ⟨z', rfl⟩ := hz
  -- x² = f·25z'² - 5y² = 5(5fz'² - y²), so 5 | x²
  have hx2 : (5 : ℤ) ∣ x ^ 2 := by
    have h1 : x ^ 2 + 5 * y ^ 2 = f * (5 * z') ^ 2 := heq
    have h2 : x ^ 2 = f * (5 * z') ^ 2 - 5 * y ^ 2 := by linarith
    refine ⟨5 * f * z' ^ 2 - y ^ 2, ?_⟩
    nlinarith
  -- 5 | x² → 5 | x (5 is prime)
  exact int_prime_five.dvd_of_dvd_pow hx2

/-- If x² + 5y² = f·z² and 5 | z and 5 | x, then 5 | y. -/
private theorem div5_y_of_div5_xz {f x y z : ℤ}
    (heq : x ^ 2 + 5 * y ^ 2 = f * z ^ 2)
    (hx : (5 : ℤ) ∣ x) (hz : (5 : ℤ) ∣ z) : (5 : ℤ) ∣ y := by
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨z', rfl⟩ := hz
  -- 25x'² + 5y² = 25fz'², so 5y² = 25(fz'² - x'²), y² = 5(fz'²-x'²)
  have hy2 : (5 : ℤ) ∣ y ^ 2 := by
    have h1 : (5 * x') ^ 2 + 5 * y ^ 2 = f * (5 * z') ^ 2 := heq
    have h2 : 5 * y ^ 2 = f * (5 * z') ^ 2 - (5 * x') ^ 2 := by linarith
    have h3 : y ^ 2 = 5 * f * z' ^ 2 - 5 * x' ^ 2 := by nlinarith
    refine ⟨f * z' ^ 2 - x' ^ 2, ?_⟩
    linarith
  exact int_prime_five.dvd_of_dvd_pow hy2

/-- Main theorem: for f ≡ 2,3 mod 5, the equation x² + 5y² = f·z²
    has no solution with z ≠ 0. Proved by infinite descent on |z|. -/
theorem not_rational_norm_mod5 (f : ℤ) (hf : f % 5 = 2 ∨ f % 5 = 3) :
    ¬ ∃ (x y z : ℤ), z ≠ 0 ∧ x ^ 2 + 5 * y ^ 2 = f * z ^ 2 := by
  intro ⟨x, y, z, hz_ne, heq⟩
  -- Descent on z.natAbs
  suffices ∀ n : ℕ, ∀ x y z : ℤ, z.natAbs = n →
      z ≠ 0 → x ^ 2 + 5 * y ^ 2 = f * z ^ 2 → False by
    exact this z.natAbs x y z rfl hz_ne heq
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro x y z hzn hz_ne heq
    have h5z := div5_of_norm_eq hf heq
    have h5x := div5_x_of_div5_z heq h5z
    have h5y := div5_y_of_div5_xz heq h5x h5z
    obtain ⟨x', rfl⟩ := h5x
    obtain ⟨y', rfl⟩ := h5y
    obtain ⟨z', rfl⟩ := h5z
    have heq' : x' ^ 2 + 5 * y' ^ 2 = f * z' ^ 2 := by nlinarith
    have hz'_ne : z' ≠ 0 := by
      intro hz'; simp [hz'] at hz_ne
    have hlt : z'.natAbs < (5 * z').natAbs := by
      rw [Int.natAbs_mul, show (5 : ℤ).natAbs = 5 from rfl]
      have : 0 < z'.natAbs := Int.natAbs_pos.mpr hz'_ne
      omega
    exact ih z'.natAbs (hzn ▸ hlt) x' y' z' rfl hz'_ne heq'

-- ========================================================================
-- Section 2: Specific non-norm results
-- ========================================================================

/-- 7 ∉ Nm(ℚ(√-5)×): the equation x² + 5y² = 7z² has no solution with z ≠ 0. -/
theorem seven_not_rational_norm_K5 :
    ¬ ∃ (x y z : ℤ), z ≠ 0 ∧ x ^ 2 + 5 * y ^ 2 = 7 * z ^ 2 :=
  not_rational_norm_mod5 7 (by norm_num)

/-- 163 ∉ Nm(ℚ(√-5)×): the equation x² + 5y² = 163z² has no solution with z ≠ 0.
    163 ≡ 3 mod 5. -/
theorem onesixtythree_not_rational_norm_K5 :
    ¬ ∃ (x y z : ℤ), z ≠ 0 ∧ x ^ 2 + 5 * y ^ 2 = 163 * z ^ 2 :=
  not_rational_norm_mod5 163 (by norm_num)

-- ========================================================================
-- Section 3: Positive norm witnesses
-- ========================================================================

/-- 9 ∈ Nm(ℚ(√-5)×): witness 2² + 5·1² = 9. Free lattice. -/
theorem nine_is_norm_K5 : ∃ (x y : ℤ), x ^ 2 + 5 * y ^ 2 = 9 :=
  ⟨2, 1, by norm_num⟩

/-- 61 ∈ Nm(ℚ(√-5)×): witness 4² + 5·3² = 61. Free lattice. -/
theorem sixtyone_is_norm_K5 : ∃ (x y : ℤ), x ^ 2 + 5 * y ^ 2 = 61 :=
  ⟨4, 3, by norm_num⟩

/-- 7/2 ∈ Nm(ℚ(√-5)×): witness 3² + 5·1² = 14 = 7·2.
    Non-free lattice with h = 7/2, Nm(𝔞) = 2. -/
theorem seven_half_is_norm_K5 :
    ∃ (x y : ℤ), x ^ 2 + 5 * y ^ 2 = 7 * 2 :=
  ⟨3, 1, by norm_num⟩

/-- 163/2 ∈ Nm(ℚ(√-5)×): witness 9² + 5·7² = 326 = 163·2.
    Non-free lattice with h = 163/2, Nm(𝔞) = 2. -/
theorem onesixtythree_half_is_norm_K5 :
    ∃ (x y : ℤ), x ^ 2 + 5 * y ^ 2 = 163 * 2 :=
  ⟨9, 7, by norm_num⟩

-- ========================================================================
-- Section 4: Steinitz class forced
-- ========================================================================

/-- For f = 7 and K = ℚ(√-5): the Steinitz class is forced non-trivial.
    Free case (h = 7) is blocked; non-free case (h = 7/2) works. -/
theorem steinitz_forced_nontrivial_K5_f7 :
    (¬ ∃ (x y z : ℤ), z ≠ 0 ∧ x ^ 2 + 5 * y ^ 2 = 7 * z ^ 2) ∧
    (∃ (x y : ℤ), x ^ 2 + 5 * y ^ 2 = 7 * 2) :=
  ⟨seven_not_rational_norm_K5, seven_half_is_norm_K5⟩

/-- For f = 163 and K = ℚ(√-5): the Steinitz class is forced non-trivial.
    Free case (h = 163) is blocked; non-free case (h = 163/2) works. -/
theorem steinitz_forced_nontrivial_K5_f163 :
    (¬ ∃ (x y z : ℤ), z ≠ 0 ∧ x ^ 2 + 5 * y ^ 2 = 163 * z ^ 2) ∧
    (∃ (x y : ℤ), x ^ 2 + 5 * y ^ 2 = 163 * 2) :=
  ⟨onesixtythree_not_rational_norm_K5, onesixtythree_half_is_norm_K5⟩

-- ========================================================================
-- Section 5: Inert conductor classification
-- ========================================================================

/-- 13 is inert in K = ℚ(√-5): x² ≡ -5 mod 13 has no solution.
    Equivalently: -5 is not a quadratic residue mod 13. -/
theorem thirteen_inert_K5 : ¬ ∃ (x : ZMod 13), x ^ 2 = -5 := by decide

/-- 19 is inert in K = ℚ(√-5). -/
theorem nineteen_inert_K5 : ¬ ∃ (x : ZMod 19), x ^ 2 = -5 := by decide

/-- 37 is inert in K = ℚ(√-5). -/
theorem thirtyseven_inert_K5 : ¬ ∃ (x : ZMod 37), x ^ 2 = -5 := by decide

/-- 79 is inert in K = ℚ(√-5). -/
theorem seventynine_inert_K5 : ¬ ∃ (x : ZMod 79), x ^ 2 = -5 := by decide

/-- 97 is inert in K = ℚ(√-5). -/
theorem ninetyseven_inert_K5 : ¬ ∃ (x : ZMod 97), x ^ 2 = -5 := by decide

-- ========================================================================
-- Section 6: Splitting witnesses for valid conductors
-- ========================================================================

/-- 7 splits in K = ℚ(√-5): x² ≡ -5 mod 7 has a solution (x = 3). -/
theorem seven_splits_K5 : ∃ (x : ZMod 7), x ^ 2 = -5 := ⟨3, by decide⟩

/-- 9 splits in K = ℚ(√-5): x² ≡ -5 mod 9 has a solution (x = 2). -/
theorem nine_splits_K5 : ∃ (x : ZMod 9), x ^ 2 = -5 := ⟨2, by decide⟩

/-- 61 splits in K = ℚ(√-5): x² ≡ -5 mod 61 has a solution (x = 19). -/
theorem sixtyone_splits_K5 : ∃ (x : ZMod 61), x ^ 2 = -5 := ⟨19, by decide⟩

/-- 163 splits in K = ℚ(√-5): x² ≡ -5 mod 163 has a solution (x = 22).
    Verification: 22² = 484 = 2·163 + 158 ≡ 158 ≡ -5 mod 163. -/
theorem onesixtythree_splits_K5 : ∃ (x : ZMod 163), x ^ 2 = -5 := ⟨22, by decide⟩
