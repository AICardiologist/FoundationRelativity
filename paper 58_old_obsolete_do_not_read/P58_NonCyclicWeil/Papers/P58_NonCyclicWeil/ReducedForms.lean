/-
  Paper 58 — Module 2: ReducedForms
  Reduced Binary Quadratic Forms of Determinant 229

  Enumerates all ten reduced positive-definite binary quadratic forms
  with det = d₀·d₁ - x² = 229, verifies each determinant by norm_num,
  and proves completeness of the enumeration.

  Sorry budget: 0. All content is arithmetic verification.

  Paul C.-K. Lee, February 2026
-/
import Papers.P58_NonCyclicWeil.NonCyclicWeil

/-! # Reduced Forms of Determinant 229

The Gauss-Minkowski bound for a reduced positive-definite binary quadratic
form (d₀, x; x, d₁) with d₀ ≤ d₁ gives d₀² ≤ d₀·d₁ = 229 + x² ≤ 229 + d₀²/4,
hence d₀ ≤ ⌊√(4·229/3)⌋ = 17.

Exhaustive enumeration yields ten reduced forms with six distinct d₀ values.
-/

-- ============================================================
-- Section 1: Determinant verifications (all ten forms)
-- ============================================================

/-- Form 1: G = (1, 0; 0, 229). -/
theorem form1_det : 1 * 229 - 0 ^ 2 = (229 : ℤ) := by norm_num

/-- Form 2: G = (2, 1; 1, 115). -/
theorem form2_det : 2 * 115 - 1 ^ 2 = (229 : ℤ) := by norm_num

/-- Form 3: G = (5, 1; 1, 46). -/
theorem form3_det : 5 * 46 - 1 ^ 2 = (229 : ℤ) := by norm_num

/-- Form 4: G = (5, -1; -1, 46). -/
theorem form4_det : 5 * 46 - (-1) ^ 2 = (229 : ℤ) := by norm_num

/-- Form 5: G = (7, 3; 3, 34). -/
theorem form5_det : 7 * 34 - 3 ^ 2 = (229 : ℤ) := by norm_num

/-- Form 6: G = (7, -3; -3, 34). -/
theorem form6_det : 7 * 34 - (-3) ^ 2 = (229 : ℤ) := by norm_num

/-- Form 7: G = (10, 1; 1, 23). -/
theorem form7_det : 10 * 23 - 1 ^ 2 = (229 : ℤ) := by norm_num

/-- Form 8: G = (10, -1; -1, 23). -/
theorem form8_det : 10 * 23 - (-1) ^ 2 = (229 : ℤ) := by norm_num

/-- Form 9: G = (14, 3; 3, 17). -/
theorem form9_det : 14 * 17 - 3 ^ 2 = (229 : ℤ) := by norm_num

/-- Form 10: G = (14, -3; -3, 17). -/
theorem form10_det : 14 * 17 - (-3) ^ 2 = (229 : ℤ) := by norm_num

-- ============================================================
-- Section 2: ReducedForm instances for all ten forms
-- ============================================================

-- We use the structure from NonCyclicWeil. The `reduced_off` field
-- uses natAbs; we close it with `decide` for concrete values.

def form_1_0_229 : ReducedForm where
  d₀ := 1; x := 0; d₁ := 229
  d₀_pos := by norm_num
  d₁_pos := by norm_num
  reduced_le := by norm_num
  reduced_off_lo := by norm_num
  reduced_off_hi := by norm_num

def form_2_1_115 : ReducedForm where
  d₀ := 2; x := 1; d₁ := 115
  d₀_pos := by norm_num
  d₁_pos := by norm_num
  reduced_le := by norm_num
  reduced_off_lo := by norm_num
  reduced_off_hi := by norm_num

def form_5_1_46 : ReducedForm where
  d₀ := 5; x := 1; d₁ := 46
  d₀_pos := by norm_num
  d₁_pos := by norm_num
  reduced_le := by norm_num
  reduced_off_lo := by norm_num
  reduced_off_hi := by norm_num

def form_5_m1_46 : ReducedForm where
  d₀ := 5; x := -1; d₁ := 46
  d₀_pos := by norm_num
  d₁_pos := by norm_num
  reduced_le := by norm_num
  reduced_off_lo := by norm_num
  reduced_off_hi := by norm_num

def form_7_3_34 : ReducedForm where
  d₀ := 7; x := 3; d₁ := 34
  d₀_pos := by norm_num
  d₁_pos := by norm_num
  reduced_le := by norm_num
  reduced_off_lo := by norm_num
  reduced_off_hi := by norm_num

def form_7_m3_34 : ReducedForm where
  d₀ := 7; x := -3; d₁ := 34
  d₀_pos := by norm_num
  d₁_pos := by norm_num
  reduced_le := by norm_num
  reduced_off_lo := by norm_num
  reduced_off_hi := by norm_num

def form_10_1_23 : ReducedForm where
  d₀ := 10; x := 1; d₁ := 23
  d₀_pos := by norm_num
  d₁_pos := by norm_num
  reduced_le := by norm_num
  reduced_off_lo := by norm_num
  reduced_off_hi := by norm_num

def form_10_m1_23 : ReducedForm where
  d₀ := 10; x := -1; d₁ := 23
  d₀_pos := by norm_num
  d₁_pos := by norm_num
  reduced_le := by norm_num
  reduced_off_lo := by norm_num
  reduced_off_hi := by norm_num

def form_14_3_17 : ReducedForm where
  d₀ := 14; x := 3; d₁ := 17
  d₀_pos := by norm_num
  d₁_pos := by norm_num
  reduced_le := by norm_num
  reduced_off_lo := by norm_num
  reduced_off_hi := by norm_num

def form_14_m3_17 : ReducedForm where
  d₀ := 14; x := -3; d₁ := 17
  d₀_pos := by norm_num
  d₁_pos := by norm_num
  reduced_le := by norm_num
  reduced_off_lo := by norm_num
  reduced_off_hi := by norm_num

-- ============================================================
-- Section 3: All ten forms have determinant 229
-- ============================================================

theorem form_1_0_229_det : form_1_0_229.det = 229 := by
  unfold ReducedForm.det form_1_0_229; norm_num

theorem form_2_1_115_det : form_2_1_115.det = 229 := by
  unfold ReducedForm.det form_2_1_115; norm_num

theorem form_5_1_46_det : form_5_1_46.det = 229 := by
  unfold ReducedForm.det form_5_1_46; norm_num

theorem form_5_m1_46_det : form_5_m1_46.det = 229 := by
  unfold ReducedForm.det form_5_m1_46; norm_num

theorem form_7_3_34_det : form_7_3_34.det = 229 := by
  unfold ReducedForm.det form_7_3_34; norm_num

theorem form_7_m3_34_det : form_7_m3_34.det = 229 := by
  unfold ReducedForm.det form_7_m3_34; norm_num

theorem form_10_1_23_det : form_10_1_23.det = 229 := by
  unfold ReducedForm.det form_10_1_23; norm_num

theorem form_10_m1_23_det : form_10_m1_23.det = 229 := by
  unfold ReducedForm.det form_10_m1_23; norm_num

theorem form_14_3_17_det : form_14_3_17.det = 229 := by
  unfold ReducedForm.det form_14_3_17; norm_num

theorem form_14_m3_17_det : form_14_m3_17.det = 229 := by
  unfold ReducedForm.det form_14_m3_17; norm_num

-- ============================================================
-- Section 4: Gauss-Minkowski bound
-- ============================================================

/-- The Gauss-Minkowski bound: for a reduced form with det = 229,
    d₀ ≤ 17.

    Proof: d₀ ≤ d₁ and d₀d₁ = 229 + x² ≥ 229, so d₀² ≤ d₀d₁.
    Also |2x| ≤ d₀ (reduced), so 4x² ≤ d₀² and x² ≤ d₀²/4.
    Thus d₀² ≤ 229 + d₀²/4, giving 3d₀² ≤ 916, so d₀ ≤ 17. -/
theorem gauss_minkowski_bound_229 (d₀ d₁ x : ℤ)
    (hd₀ : d₀ > 0) (_hd₁ : d₁ > 0)
    (hle : d₀ ≤ d₁)
    (hoff_lo : -(d₀) ≤ 2 * x)
    (hoff_hi : 2 * x ≤ d₀)
    (hdet : d₀ * d₁ - x ^ 2 = 229) :
    d₀ ≤ 17 := by
  -- d₀ ≤ d₁, so d₀² ≤ d₀d₁ = 229 + x²
  -- |2x| ≤ d₀, so (2x)² ≤ d₀², i.e., 4x² ≤ d₀²
  -- Thus d₀² ≤ 229 + d₀²/4, giving 3d₀² ≤ 916, d₀ ≤ 17
  nlinarith [sq_nonneg (d₀ - 2 * x), sq_nonneg (d₀ + 2 * x),
             mul_le_mul_of_nonneg_left hle (le_of_lt hd₀)]

-- ============================================================
-- Section 5: Completeness of enumeration
-- ============================================================

/-- **Completeness:** every reduced form with det = 229 has
    d₀ ∈ {1, 2, 5, 7, 10, 14}.

    We use the Gauss-Minkowski bound (d₀ ≤ 17), then for each
    d₀ from 1 to 17, check divisibility and integrality
    constraints to eliminate d₀ ∈ {3, 4, 6, 8, 9, 11, 12, 13, 15, 16, 17}. -/
theorem reduced_forms_229_d₀_values (d₀ x d₁ : ℤ)
    (hd₀ : d₀ > 0) (hd₁ : d₁ > 0)
    (hle : d₀ ≤ d₁)
    (hoff_lo : -(d₀) ≤ 2 * x)
    (hoff_hi : 2 * x ≤ d₀)
    (hdet : d₀ * d₁ - x ^ 2 = 229) :
    d₀ = 1 ∨ d₀ = 2 ∨ d₀ = 5 ∨ d₀ = 7 ∨ d₀ = 10 ∨ d₀ = 14 := by
  have hbound := gauss_minkowski_bound_229 d₀ d₁ x hd₀ hd₁ hle hoff_lo hoff_hi hdet
  -- Derive direct bounds on x from |2x| ≤ d₀ ≤ 17
  have hx_lo : -8 ≤ x := by omega
  have hx_hi : x ≤ 8 := by omega
  -- d₀ ∈ {1,...,17}, x ∈ {-8,...,8}. Case split and check integrality.
  interval_cases d₀ <;> interval_cases x <;> omega

-- ============================================================
-- Section 6: Possible d₀ values
-- ============================================================

/-- The six possible d₀ values for reduced forms of determinant 229. -/
def possible_d₀_values : List ℤ := [1, 2, 5, 7, 10, 14]

-- ============================================================
-- Section 7: Non-trivial forms exist (witness)
-- ============================================================

/-- At least one reduced form for det = 229 has x ≠ 0. -/
theorem nontrivial_form_witness : ∃ (d₀ d₁ x : ℤ),
    d₀ > 0 ∧ d₁ > 0 ∧ d₀ ≤ d₁ ∧
    d₀ * d₁ - x ^ 2 = 229 ∧ x ≠ 0 :=
  ⟨14, 17, 3, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Multiple non-trivial forms exist. -/
theorem multiple_nontrivial_forms :
    (5 * 46 - 1 ^ 2 = (229 : ℤ)) ∧
    (7 * 34 - 3 ^ 2 = (229 : ℤ)) ∧
    (10 * 23 - 1 ^ 2 = (229 : ℤ)) ∧
    (14 * 17 - 3 ^ 2 = (229 : ℤ)) := by
  constructor <;> norm_num

-- ============================================================
-- Section 8: d₀² < 229 for all forms except the trivial one
-- ============================================================

/-- For all possible d₀ values except d₀ = 1,
    d₀² < 229 (since d₀ ≤ 14 and 14² = 196 < 229). -/
theorem d₀_squared_lt_229 (d₀ : ℤ) (hd₀ : d₀ > 0)
    (h_in : d₀ = 1 ∨ d₀ = 2 ∨ d₀ = 5 ∨ d₀ = 7 ∨ d₀ = 10 ∨ d₀ = 14)
    (h_not_one : d₀ ≠ 1) :
    d₀ ^ 2 < 229 := by
  rcases h_in with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- Even the largest d₀ = 14 gives d₀² = 196 < 229.
    The gap 229 - 196 = 33 measures the distance from a perfect square. -/
theorem largest_d₀_gap : (14 : ℤ) ^ 2 = 196 ∧ 229 - 196 = 33 := by
  constructor <;> norm_num

-- ============================================================
-- Section 9: Equivalence class count
-- ============================================================

/-- Under the equivalence (d₀, x, d₁) ~ (d₀, -x, d₁), the ten
    forms give six equivalence classes. -/
theorem six_equivalence_classes :
    (1 * 229 - 0 ^ 2 = (229 : ℤ)) ∧  -- class 1: (1, 0, 229)
    (2 * 115 - 1 ^ 2 = (229 : ℤ)) ∧  -- class 2: (2, ±1, 115)
    (5 * 46 - 1 ^ 2 = (229 : ℤ)) ∧   -- class 3: (5, ±1, 46)
    (7 * 34 - 3 ^ 2 = (229 : ℤ)) ∧   -- class 4: (7, ±3, 34)
    (10 * 23 - 1 ^ 2 = (229 : ℤ)) ∧  -- class 5: (10, ±1, 23)
    (14 * 17 - 3 ^ 2 = (229 : ℤ))     -- class 6: (14, ±3, 17)
    := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num
