/-
  Paper 30: The Physical Dispensability of the Fan Theorem
  SupExists.lean — BMC implies supremum existence + ε-attainment

  Main theorem:
    sup_exists_of_bmc : BMC → ∀ f a b, a < b → ContinuousOn f (Icc a b) →
      ∃ S, (∀ y ∈ Icc a b, f y ≤ S) ∧ (∀ ε > 0, ∃ x ∈ Icc a b, S − ε < f x)

  Proof strategy:
    1. f is bounded on [a,b] (compactness)
    2. runningGridMax is monotone + bounded → BMC gives limit S
    3. S is an upper bound: uniform continuity + grid density → contradiction
    4. S is ε-attainable: T_n → S and each T_n is witnessed by a grid point
-/
import Papers.P30_FTDispensability.GridApprox

noncomputable section
namespace Papers.P30

open Set Finset Metric

-- ========================================================================
-- Key helper: f is bounded on [a,b]
-- ========================================================================

/-- A continuous function on [a,b] is bounded above. -/
theorem bddAbove_of_continuousOn {f : ℝ → ℝ} {a b : ℝ} (_hab : a < b)
    (hf : ContinuousOn f (Icc a b)) :
    ∃ M : ℝ, ∀ y ∈ Icc a b, f y ≤ M := by
  have hcpt : IsCompact (Icc a b) := isCompact_Icc
  have hbdd : BddAbove (f '' Icc a b) :=
    (hcpt.image_of_continuousOn hf).isBounded.bddAbove
  obtain ⟨M, hM⟩ := hbdd
  exact ⟨M, fun y hy => hM (Set.mem_image_of_mem f hy)⟩

-- ========================================================================
-- Helper: running grid max witness extraction
-- ========================================================================

/-- T_n is attained by gridMaxVal at some step m ≤ n. -/
theorem runningGridMax_witness (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    ∃ m, m ≤ n ∧ runningGridMax f a b n = gridMaxVal f a b m := by
  induction n with
  | zero => exact ⟨0, le_refl _, rfl⟩
  | succ n ih =>
    simp only [runningGridMax]
    by_cases h : runningGridMax f a b n ≤ gridMaxVal f a b (n + 1)
    · rw [max_eq_right h]; exact ⟨n + 1, le_refl _, rfl⟩
    · push_neg at h; rw [max_eq_left (le_of_lt h)]
      obtain ⟨m, hm_le, hm_eq⟩ := ih
      exact ⟨m, Nat.le_succ_of_le hm_le, hm_eq⟩

/-- gridMaxVal at step m is witnessed at a point in [a,b]. -/
theorem gridMaxVal_witness_mem {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (m : ℕ) :
    ∃ x ∈ Icc a b, gridMaxVal f a b m = f x := by
  obtain ⟨k, hk_le, hk_eq⟩ := gridMaxVal_exists_witness f a b m
  exact ⟨gridPoint a b (m + 1) k,
    gridPoint_mem_Icc (le_of_lt hab) (Nat.succ_pos m) (by omega : k ≤ m + 1),
    hk_eq⟩

-- ========================================================================
-- Grid approximation lemma
-- ========================================================================

/-- For any y ∈ [a,b] and large enough grid, there is a grid point near y
    whose index is ≤ n (compatible with gridMaxVal f a b n). -/
theorem grid_density_for_gridMaxVal {a b : ℝ} (hab : a < b) {y : ℝ} (hy : y ∈ Icc a b)
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ k, k ≤ n ∧ gridPoint a b (n + 1) k ∈ Icc a b ∧
      |y - gridPoint a b (n + 1) k| ≤ (b - a) / ↑(n + 1) := by
  -- Use grid_density with parameter (n+1), giving k' ≤ n+1
  obtain ⟨k', hk'_le, hk'_close⟩ := grid_density hab hy (Nat.succ_pos n)
  -- If k' ≤ n, we're done
  by_cases hk'n : k' ≤ n
  · exact ⟨k', hk'n,
      gridPoint_mem_Icc (le_of_lt hab) (Nat.succ_pos n) (by omega),
      hk'_close⟩
  · -- k' = n+1, so gridPoint a b (n+1) (n+1) = b
    -- Use k = n instead: gridPoint a b (n+1) n
    -- |y - gridPoint(n)| ≤ |y - b| + |b - gridPoint(n)|
    -- gridPoint a b (n+1) n = a + n*(b-a)/(n+1)
    -- b - gridPoint(n) = b - a - n*(b-a)/(n+1) = (b-a)/(n+1)
    -- |y - gridPoint(n)| ≤ |y - b| + (b-a)/(n+1)
    -- But |y - b| ≤ |y - gridPoint(n+1)| ≤ (b-a)/(n+1)
    -- So |y - gridPoint(n)| ≤ 2*(b-a)/(n+1)
    -- Hmm, this doubles the error. Let me think again.
    -- Actually k' = n+1 means y is closest to b.
    -- gridPoint(n) is at distance (b-a)/(n+1) from b.
    -- So |y - gridPoint(n)| ≤ |y - b| + |b - gridPoint(n)|
    --   ≤ (b-a)/(n+1) + (b-a)/(n+1) = 2*(b-a)/(n+1)
    -- We need the bound to be (b-a)/(n+1). So the factor of 2 is a problem.
    -- But actually, grid_density already guarantees |y - gridPoint(k')| ≤ (b-a)/(n+1).
    -- When k' = n+1, gridPoint(n+1) = a + (n+1)*(b-a)/(n+1) = b.
    -- So |y - b| ≤ (b-a)/(n+1).
    -- Now gridPoint(n) = a + n*(b-a)/(n+1) = b - (b-a)/(n+1).
    -- |y - gridPoint(n)| = |y - b + (b-a)/(n+1)|
    --   ≤ |y - b| + (b-a)/(n+1) ≤ 2*(b-a)/(n+1).
    -- This is suboptimal but still works — we just need a sufficiently large grid.
    -- Actually, we only need the DISTANCE to be small, and we're choosing n freely.
    -- So the factor of 2 doesn't matter — just use a grid twice as fine.
    -- But for now, let's just accept the factor of 2 bound:
    have hk' : k' = n + 1 := by omega
    use n
    refine ⟨le_refl n,
      gridPoint_mem_Icc (le_of_lt hab) (Nat.succ_pos n) (by omega),
      ?_⟩
    -- gridPoint a b (n+1) (n+1) = b, and gridPoint a b (n+1) n = b - (b-a)/(n+1)
    have hba_pos : (0:ℝ) < b - a := sub_pos.mpr hab
    have hn1_pos : (0:ℝ) < ↑(n + 1) := Nat.cast_pos.mpr (Nat.succ_pos n)
    -- y is close to b: |y - b| ≤ (b-a)/(n+1) (from k' = n+1)
    have hy_near_b : |y - b| ≤ (b - a) / ↑(n + 1) := by
      have : gridPoint a b (n + 1) (n + 1) = b := by
        unfold gridPoint; field_simp; ring
      rw [hk'] at hk'_close; rwa [this] at hk'_close
    -- Actually, since a ≤ y ≤ b and gridPoint(n) ≤ b, we have:
    -- gridPoint(n) ≤ y is possible, and y ≤ b.
    -- |y - gridPoint(n)| = y - gridPoint(n) (if y ≥ gridPoint(n))
    --   = (y - b) + (b - gridPoint(n))
    --   ≤ 0 + (b-a)/(n+1) = (b-a)/(n+1)
    -- Since y ≤ b (from y ∈ [a,b]).
    -- So actually |y - gridPoint(n)| ≤ (b - a)/(n+1)! Great.
    -- This is because y is between gridPoint(n) and gridPoint(n+1) = b.
    have hgp_n : gridPoint a b (n + 1) n = b - (b - a) / ↑(n + 1) := by
      unfold gridPoint
      have hne : (↑(n + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      -- Goal: a + ↑n * (b - a) / ↑(n + 1) = b - (b - a) / ↑(n + 1)
      -- ↔ a + ↑n * (b - a) / ↑(n + 1) + (b - a) / ↑(n + 1) = b
      -- ↔ a + (↑n + 1) * (b - a) / ↑(n + 1) = b
      -- ↔ a + (b - a) = b ✓
      have key : ↑n * (b - a) / ↑(n + 1) + (b - a) / ↑(n + 1) = b - a := by
        rw [← add_div]
        conv_lhs => rw [show ↑n * (b - a) + (b - a) = (b - a) * (↑n + 1) from by ring,
          show (↑n : ℝ) + 1 = ↑(n + 1) from by push_cast; ring]
        exact mul_div_cancel_of_imp fun h => absurd h hne
      linarith
    rw [hgp_n]
    have hy_le_b : y ≤ b := hy.2
    have hgp_le_y : b - (b - a) / ↑(n + 1) ≤ y := by
      -- From |y - b| ≤ (b-a)/(n+1), we get -(b-a)/(n+1) ≤ y - b
      have h_abs := (abs_le.mp hy_near_b).1
      -- h_abs : -(b-a)/↑(n+1) ≤ y - b, so b - (b-a)/↑(n+1) ≤ y
      linarith
    rw [abs_of_nonneg (by linarith)]
    linarith

-- ========================================================================
-- Main theorem: BMC → supremum exists + ε-attainment
-- ========================================================================

/-- BMC implies the approximate extreme value theorem. -/
theorem sup_exists_of_bmc (hbmc : BMC) :
    ∀ (f : ℝ → ℝ) (a b : ℝ), a < b → ContinuousOn f (Icc a b) →
      ∃ S : ℝ, (∀ y ∈ Icc a b, f y ≤ S) ∧
        ∀ ε : ℝ, 0 < ε → ∃ x ∈ Icc a b, S - ε < f x := by
  intro f a b hab hf
  obtain ⟨M, hM⟩ := bddAbove_of_continuousOn hab hf
  have hT_mono := runningGridMax_mono f a b
  have hT_bdd := runningGridMax_bounded (le_of_lt hab) hM
  obtain ⟨S, hS_lim⟩ := hbmc (runningGridMax f a b) M hT_mono hT_bdd
  -- S is an upper bound
  have hS_ub : ∀ y ∈ Icc a b, f y ≤ S := by
    intro y hy
    by_contra h_neg
    push_neg at h_neg
    set δ := f y - S
    have hδ_pos : 0 < δ := by linarith
    have hδ2 : (0:ℝ) < δ / 2 := by linarith
    -- Uniform continuity
    have huc := isCompact_Icc.uniformContinuousOn_of_continuous hf
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨η, hη_pos, hη_uc⟩ := huc (δ / 2) hδ2
    -- Choose N such that grid spacing < η and |T_N - S| < δ/2
    obtain ⟨N₁, hN₁⟩ := exists_nat_gt ((b - a) / η)
    obtain ⟨N₀, hN₀⟩ := hS_lim (δ / 2) hδ2
    set N := max N₀ N₁ + 1  -- ensure N ≥ 1
    -- Grid spacing bound
    have hN_pos : 0 < N := by omega
    have hN1_pos : (0:ℝ) < ↑(N + 1) := Nat.cast_pos.mpr (Nat.succ_pos N)
    have hgrid_small : (b - a) / ↑(N + 1) < η := by
      have hba_pos : (0:ℝ) < b - a := sub_pos.mpr hab
      have hN1_ge : (↑N₁ + 1 : ℝ) ≤ ↑(N + 1) := by
        have : N₁ + 1 ≤ N + 1 := by
          have := le_max_right N₀ N₁; omega
        exact_mod_cast this
      calc (b - a) / ↑(N + 1) ≤ (b - a) / (↑N₁ + 1) := by
            apply div_le_div_of_nonneg_left hba_pos.le
              (by positivity) hN1_ge
        _ < η := by
          rw [div_lt_iff₀ (by positivity : (0:ℝ) < ↑N₁ + 1)]
          have h1 : (b - a) / η < ↑N₁ := hN₁
          rw [div_lt_iff₀ hη_pos] at h1
          -- h1 : b - a < ↑N₁ * η, goal : b - a < (↑N₁ + 1) * η
          nlinarith
    -- Get nearby grid point with k ≤ N
    obtain ⟨k, hk_le, hk_mem, hk_close⟩ := grid_density_for_gridMaxVal hab hy (by omega : 1 ≤ N)
    -- dist(gp, y) < η
    have hdist : dist (gridPoint a b (N + 1) k) y < η := by
      rw [Real.dist_eq, abs_sub_comm]
      exact lt_of_le_of_lt hk_close hgrid_small
    -- |f(gp) - f(y)| < δ/2
    have hf_close := hη_uc (gridPoint a b (N + 1) k) hk_mem y hy hdist
    rw [Real.dist_eq] at hf_close
    -- f(gp) > S + δ/2
    have hf_gp : f (gridPoint a b (N + 1) k) > S + δ / 2 := by
      have := (abs_lt.mp hf_close).1; linarith
    -- gridMaxVal N ≥ f(gp)
    have hgm := le_gridMaxVal f a b N hk_le
    -- T_N ≥ gridMaxVal N
    have hTN := gridMaxVal_le_runningGridMax f a b N
    -- T_N > S + δ/2
    have hTN_big : runningGridMax f a b N > S + δ / 2 := by linarith
    -- But |T_N - S| < δ/2
    have hN₀_le : N₀ ≤ N := by omega
    have := hN₀ N hN₀_le
    rw [abs_lt] at this
    linarith [this.2]
  -- S is ε-attainable
  have hS_approx : ∀ ε : ℝ, 0 < ε → ∃ x ∈ Icc a b, S - ε < f x := by
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := hS_lim ε hε
    have hN := hN₀ N₀ (le_refl N₀)
    have hT_close : S - ε < runningGridMax f a b N₀ := by
      rw [abs_lt] at hN; linarith [hN.1]
    obtain ⟨m, _, hm_eq⟩ := runningGridMax_witness f a b N₀
    obtain ⟨x, hx_mem, hx_eq⟩ := gridMaxVal_witness_mem hab m
    exact ⟨x, hx_mem, by linarith [hm_eq, hx_eq]⟩
  exact ⟨S, hS_ub, hS_approx⟩

end Papers.P30
end
