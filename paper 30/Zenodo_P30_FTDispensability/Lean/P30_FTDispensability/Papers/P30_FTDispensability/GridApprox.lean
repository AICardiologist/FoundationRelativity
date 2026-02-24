/-
  Paper 30: The Physical Dispensability of the Fan Theorem
  GridApprox.lean — Grid construction and approximation properties

  Key lemmas:
    - gridPoint_mem_Icc: grid points lie in [a,b]
    - gridMaxVal_le_bound: grid max respects upper bounds
    - gridMaxVal_exists_witness: grid max is attained at some grid point
    - runningGridMax_mono: running max is monotone
    - runningGridMax_bounded: running max is bounded above
    - grid_density: for any x ∈ [a,b], some grid point is within (b-a)/n

  These are the building blocks for the BMC → supremum argument in SupExists.lean.
-/
import Papers.P30_FTDispensability.Defs

noncomputable section
namespace Papers.P30

open Set Finset

-- ========================================================================
-- Grid points lie in [a,b]
-- ========================================================================

/-- Grid points lie in [a,b] when k ≤ n and a ≤ b. -/
theorem gridPoint_mem_Icc {a b : ℝ} (hab : a ≤ b) {n : ℕ} (hn : 0 < n)
    {k : ℕ} (hk : k ≤ n) : gridPoint a b n k ∈ Icc a b := by
  unfold gridPoint
  have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  constructor
  · have : 0 ≤ ↑k * (b - a) / ↑n := by
      apply div_nonneg
      · exact mul_nonneg (Nat.cast_nonneg k) (sub_nonneg.mpr hab)
      · exact le_of_lt hn'
    linarith
  · have hkn : (↑k : ℝ) ≤ ↑n := Nat.cast_le.mpr hk
    have : ↑k * (b - a) / ↑n ≤ b - a := by
      rw [div_le_iff₀ hn']
      nlinarith
    linarith

-- ========================================================================
-- Grid max respects upper bounds
-- ========================================================================

/-- If f ≤ M on [a,b], then gridMaxVal f a b n ≤ M. -/
theorem gridMaxVal_le_bound {f : ℝ → ℝ} {a b : ℝ} {M : ℝ} (hab : a ≤ b)
    (hfM : ∀ y ∈ Icc a b, f y ≤ M) (n : ℕ) :
    gridMaxVal f a b n ≤ M := by
  unfold gridMaxVal
  apply Finset.max'_le
  intro v hv
  rw [Finset.mem_image] at hv
  obtain ⟨k, hk_mem, rfl⟩ := hv
  rw [Finset.mem_range] at hk_mem
  apply hfM
  apply gridPoint_mem_Icc hab (Nat.succ_pos n)
  omega

/-- gridMaxVal is witnessed by some grid point. -/
theorem gridMaxVal_exists_witness (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    ∃ k, k ≤ n ∧ gridMaxVal f a b n = f (gridPoint a b (n + 1) k) := by
  unfold gridMaxVal
  set S := (Finset.range (n + 1)).image (fun k => f (gridPoint a b (n + 1) k))
  have hne : S.Nonempty := ⟨f (gridPoint a b (n + 1) 0),
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n), rfl⟩⟩
  have hmem := Finset.max'_mem S hne
  rw [Finset.mem_image] at hmem
  obtain ⟨k, hk_mem, hk_eq⟩ := hmem
  rw [Finset.mem_range] at hk_mem
  exact ⟨k, by omega, hk_eq.symm⟩

-- ========================================================================
-- Running grid max is monotone
-- ========================================================================

/-- Running grid max is monotone (non-decreasing). -/
theorem runningGridMax_mono (f : ℝ → ℝ) (a b : ℝ) :
    Monotone (runningGridMax f a b) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [runningGridMax]
  exact le_max_left _ _

/-- Running grid max is bounded above if f is bounded on [a,b]. -/
theorem runningGridMax_bounded {f : ℝ → ℝ} {a b : ℝ} {M : ℝ} (hab : a ≤ b)
    (hfM : ∀ y ∈ Icc a b, f y ≤ M) (n : ℕ) :
    runningGridMax f a b n ≤ M := by
  induction n with
  | zero => exact gridMaxVal_le_bound hab hfM 0
  | succ n ih =>
    simp only [runningGridMax]
    exact max_le ih (gridMaxVal_le_bound hab hfM (n + 1))

-- ========================================================================
-- Grid density
-- ========================================================================

/-- For any x ∈ [a,b] with a < b, and any n ≥ 1, there exists a grid point
    within distance (b-a)/n of x. -/
theorem grid_density {a b : ℝ} (hab : a < b) {x : ℝ} (hx : x ∈ Icc a b)
    {n : ℕ} (hn : 0 < n) :
    ∃ k, k ≤ n ∧ |x - gridPoint a b n k| ≤ (b - a) / ↑n := by
  have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hba : 0 < b - a := sub_pos.mpr hab
  have hne_n : (↑n : ℝ) ≠ 0 := ne_of_gt hn'
  -- Normalize: let t = (x - a) / (b - a) ∈ [0,1]
  set t := (x - a) / (b - a) with ht_def
  have ht_nn : 0 ≤ t := div_nonneg (sub_nonneg.mpr hx.1) (le_of_lt hba)
  have ht_le : t ≤ 1 := by
    rw [div_le_one hba]; linarith [hx.2]
  have h_tn_nn : 0 ≤ t * ↑n := mul_nonneg ht_nn (le_of_lt hn')
  -- ⌊t*n⌋ ≤ n since t ≤ 1
  have hfl_le : Nat.floor (t * ↑n) ≤ n := by
    apply Nat.floor_le_of_le
    nlinarith
  set k := Nat.floor (t * ↑n) with hk_def
  use k
  constructor
  · exact hfl_le
  · -- gridPoint a b n k = a + k * (b - a) / n
    unfold gridPoint
    -- x - a = t * (b - a)
    have hxa : x - a = t * (b - a) := by
      rw [ht_def]; field_simp
    -- We need: |x - (a + k*(b-a)/n)| ≤ (b-a)/n
    -- = |(x - a) - k*(b-a)/n|
    -- = |t*(b-a) - k*(b-a)/n|
    -- = (b-a) * |t - k/n|
    -- = (b-a)/n * |t*n - k|
    -- And |t*n - ⌊t*n⌋| ≤ 1, so this ≤ (b-a)/n
    have key : |x - (a + ↑k * (b - a) / ↑n)| = (b - a) / ↑n * |t * ↑n - ↑k| := by
      have hxa' : x = a + t * (b - a) := by linarith
      have : x - (a + ↑k * (b - a) / ↑n) = (b - a) / ↑n * (t * ↑n - ↑k) := by
        rw [hxa']; field_simp; ring
      rw [this, abs_mul, abs_of_pos (div_pos hba hn')]
    rw [key]
    -- |t*n - ⌊t*n⌋| ≤ 1
    have hfl := Nat.floor_le h_tn_nn  -- ⌊t*n⌋ ≤ t*n
    have hlt := Nat.lt_floor_add_one (t * ↑n)  -- t*n < ⌊t*n⌋ + 1
    have h_abs_le : |t * ↑n - ↑k| ≤ 1 := by
      rw [abs_le]
      constructor
      · linarith
      · linarith
    calc (b - a) / ↑n * |t * ↑n - ↑k|
        ≤ (b - a) / ↑n * 1 := by
          apply mul_le_mul_of_nonneg_left h_abs_le (le_of_lt (div_pos hba hn'))
      _ = (b - a) / ↑n := mul_one _

/-- For any x ∈ [a,b] with a < b, and any n ≥ 1, there exists a grid point
    in [a,b] within distance (b-a)/n of x. -/
theorem grid_density_mem {a b : ℝ} (hab : a < b) {x : ℝ} (hx : x ∈ Icc a b)
    {n : ℕ} (hn : 0 < n) :
    ∃ k, k ≤ n ∧ gridPoint a b n k ∈ Icc a b ∧
      |x - gridPoint a b n k| ≤ (b - a) / ↑n := by
  obtain ⟨k, hk_le, hk_close⟩ := grid_density hab hx hn
  exact ⟨k, hk_le, gridPoint_mem_Icc (le_of_lt hab) hn hk_le, hk_close⟩

-- ========================================================================
-- Grid max is at least as big as f at any grid point
-- ========================================================================

/-- gridMaxVal f a b n ≥ f at any grid point k ≤ n. -/
theorem le_gridMaxVal (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) {k : ℕ} (hk : k ≤ n) :
    f (gridPoint a b (n + 1) k) ≤ gridMaxVal f a b n := by
  unfold gridMaxVal
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩

/-- The running grid max at step n is at least gridMaxVal at step n. -/
theorem gridMaxVal_le_runningGridMax (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    gridMaxVal f a b n ≤ runningGridMax f a b n := by
  cases n with
  | zero => exact le_refl _
  | succ n => exact le_max_right _ _

end Papers.P30
end
