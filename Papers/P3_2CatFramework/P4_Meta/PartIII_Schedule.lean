/-
  Papers/P3_2CatFramework/P4_Meta/PartIII_Schedule.lean
  
  Schedule and quota invariants for k-ary proof height calculus.
  This generalizes the parity obstruction used in 2-axis case to
  arbitrary periodic schedules.
-/
import Papers.P3_2CatFramework.P4_Meta.PartIII_ProductHeight

namespace Papers.P4Meta

/-! ### Schedule definitions

A schedule determines which axis contributes at each stage.
For k axes, we map stage indices to axis indices.
-/

/-- A schedule assigns each stage to one of k axes. -/
structure Schedule (k : Nat) where
  assign : Nat → Fin k

/-- Round-robin schedule: axis i appears at stages k*n + i. -/
def roundRobin (k : Nat) (hk : k > 0) : Schedule k :=
{ assign := fun n => ⟨n % k, Nat.mod_lt n hk⟩ }

/-- Even/odd schedule for k=2 (our existing fuseSteps). -/
def evenOddSchedule : Schedule 2 :=
roundRobin 2 (by decide)

@[simp] theorem evenOddSchedule_even (n : Nat) :
  (evenOddSchedule.assign (2 * n)).val = 0 := by
  simp [evenOddSchedule, roundRobin, Nat.mul_mod_right]

@[simp] theorem evenOddSchedule_odd (n : Nat) :
  (evenOddSchedule.assign (2 * n + 1)).val = 1 := by
  simp [evenOddSchedule, roundRobin, Nat.add_mod, Nat.mul_mod_right]

/-! ### Quota invariants

For a schedule σ and stage m, quota_i(m) counts how many times
axis i has appeared in stages < m.
-/

/-- Quota: how many times axis `i` has fired strictly before stage `m`. -/
def quota {k} (σ : Schedule k) (i : Fin k) (m : Nat) : Nat :=
  (List.range m).filter (fun n => σ.assign n = i) |>.length

@[simp] theorem quota_zero {k} (σ : Schedule k) (i : Fin k) :
  quota σ i 0 = 0 := by
  unfold quota; simp

/-- One-step recursion for quotas. -/
theorem quota_succ {k} (σ : Schedule k) (i : Fin k) (m : Nat) :
  quota σ i (m+1) = quota σ i m + (if σ.assign m = i then 1 else 0) := by
  classical
  unfold quota
  by_cases h : σ.assign m = i
  · -- `range (m+1) = range m ++ [m]` and the last singleton contributes 1
    simp [List.range_succ, List.filter_append, h]
  · -- same but the last singleton contributes 0
    simp [List.range_succ, List.filter_append, h]

/-! ### Even/odd schedule ↔ fuseSteps (k = 2) -/

/-- Axis picker for the even/odd schedule using pattern matching. -/
def evenOddAxes (A B : Nat → Formula) : Fin 2 → (Nat → Formula)
  | ⟨0, _⟩ => A
  | ⟨1, _⟩ => B
  | ⟨n+2, h⟩ => absurd h (by simp : ¬(n + 2 < 2))

/-- Pattern matching on axis 0 selects A. -/
@[simp] theorem evenOddAxes_zero (A B : Nat → Formula) :
  evenOddAxes A B ⟨0, by decide⟩ = A := rfl

/-- Pattern matching on axis 1 selects B. -/
@[simp] theorem evenOddAxes_one (A B : Nat → Formula) :
  evenOddAxes A B ⟨1, by decide⟩ = B := rfl

/-- Round-robin on k=2 assigns axis 0 at even stages. -/
@[simp] theorem evenOdd_assign_even (n : Nat) :
  evenOddSchedule.assign (2*n) = (⟨0, by decide⟩ : Fin 2) := by
  apply Fin.ext
  -- `roundRobin 2` assigns `n % 2`, so `2*n % 2 = 0`
  simp [evenOddSchedule, roundRobin, Nat.mul_mod_right]

/-- Round-robin on k=2 assigns axis 1 at odd stages. -/
@[simp] theorem evenOdd_assign_odd (n : Nat) :
  evenOddSchedule.assign (2*n+1) = (⟨1, by decide⟩ : Fin 2) := by
  apply Fin.ext
  -- `2*n+1 % 2 = 1`
  simp [evenOddSchedule, roundRobin, Nat.add_mod, Nat.mul_mod_right]

/-- Two-step increment: axis 0's quota increases by exactly 1 between even stages. -/
theorem quota_evenOdd_zero_step (n : Nat) :
  quota evenOddSchedule (⟨0, by decide⟩ : Fin 2) (2*n+2)
    = quota evenOddSchedule (⟨0, by decide⟩ : Fin 2) (2*n) + 1 := by
  classical
  have t1 :
      quota evenOddSchedule ⟨0, by decide⟩ (2*n+1)
        = quota evenOddSchedule ⟨0, by decide⟩ (2*n) + 1 := by
    -- step from 2n → 2n+1: index `m = 2n` is even, axis 0 fires
    simpa [evenOdd_assign_even n] using
      quota_succ (σ := evenOddSchedule) (i := ⟨0, by decide⟩) (m := 2*n)
  have t2 :
      quota evenOddSchedule ⟨0, by decide⟩ (2*n+2)
        = quota evenOddSchedule ⟨0, by decide⟩ (2*n+1) + 0 := by
    -- step from 2n+1 → 2n+2: index `m = 2n+1` is odd, axis 1 fires
    simpa [evenOdd_assign_odd n] using
      quota_succ (σ := evenOddSchedule) (i := ⟨0, by decide⟩) (m := 2*n+1)
  calc
    quota evenOddSchedule ⟨0, by decide⟩ (2*n+2)
        = quota evenOddSchedule ⟨0, by decide⟩ (2*n+1) + 0 := t2
    _   = (quota evenOddSchedule ⟨0, by decide⟩ (2*n) + 1) + 0 := by rw [t1]
    _   = quota evenOddSchedule ⟨0, by decide⟩ (2*n) + 1 := by simp

/-- Quota for axis 0 at even stages: exactly `n` occurrences. -/
@[simp] theorem quota_evenOdd_zero_even (n : Nat) :
  quota evenOddSchedule (⟨0, by decide⟩ : Fin 2) (2*n) = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- rewrite 2*(n+1) as 2*n+2 and use the two-step lemma
    have : 2*(n+1) = 2*n+2 := by simp [Nat.mul_succ]
    rw [this]
    rw [quota_evenOdd_zero_step]
    rw [ih]

/-- Two-step increment: axis 1's quota increases by exactly 1 between odd stages. -/
theorem quota_evenOdd_one_step (n : Nat) :
  quota evenOddSchedule (⟨1, by decide⟩ : Fin 2) (2*n+3)
    = quota evenOddSchedule (⟨1, by decide⟩ : Fin 2) (2*n+1) + 1 := by
  classical
  have t1 :
      quota evenOddSchedule ⟨1, by decide⟩ (2*n+2)
        = quota evenOddSchedule ⟨1, by decide⟩ (2*n+1) + 1 := by
    -- step from 2n+1 → 2n+2: index `m = 2n+1` is odd, axis 1 fires
    simpa [evenOdd_assign_odd n] using
      quota_succ (σ := evenOddSchedule) (i := ⟨1, by decide⟩) (m := 2*n+1)
  have t2 :
      quota evenOddSchedule ⟨1, by decide⟩ (2*n+3)
        = quota evenOddSchedule ⟨1, by decide⟩ (2*n+2) + 0 := by
    -- step from 2n+2 → 2n+3: index `m = 2n+2` is even, axis 0 fires
    have h : evenOddSchedule.assign (2*n+2) = (⟨0, by decide⟩ : Fin 2) := by
      -- direct use of the even lemma with `(n+1)`, avoiding `convert`
      apply Fin.ext; simp [evenOddSchedule, roundRobin, Nat.mul_mod_right]
    simpa [h] using
      quota_succ (σ := evenOddSchedule) (i := ⟨1, by decide⟩) (m := 2*n+2)
  calc
    quota evenOddSchedule ⟨1, by decide⟩ (2*n+3)
        = quota evenOddSchedule ⟨1, by decide⟩ (2*n+2) + 0 := t2
    _   = (quota evenOddSchedule ⟨1, by decide⟩ (2*n+1) + 1) + 0 := by rw [t1]
    _   = quota evenOddSchedule ⟨1, by decide⟩ (2*n+1) + 1 := by simp

/-- Quota for axis 1 at odd stages: exactly `n` occurrences. -/
@[simp] theorem quota_evenOdd_one_odd (n : Nat) :
  quota evenOddSchedule (⟨1, by decide⟩ : Fin 2) (2*n+1) = n := by
  induction n with
  | zero =>
    -- base: at stage 1 we only saw axis 0 at stage 0, so quota_1(1) = 0
    have h0 := quota_succ (σ := evenOddSchedule) (i := ⟨1, by decide⟩) (m := 0)
    have hA : evenOddSchedule.assign 0 = (⟨0, by decide⟩ : Fin 2) := by
      simpa using evenOdd_assign_even 0
    simpa [quota_zero, hA]
      using h0
  | succ n ih =>
    -- rewrite 2*(n+1)+1 as 2*n+3 and use the two-step lemma
    have : 2*(n+1)+1 = 2*n+3 := by
      rw [Nat.mul_succ]
    rw [this]
    rw [quota_evenOdd_one_step]
    rw [ih]

/-! ### Schedule composition -/

/-- Apply a schedule to k axes to get a single step function. -/
def scheduleSteps {k : Nat} (σ : Schedule k) (axes : Fin k → (Nat → Formula)) : Nat → Formula :=
  fun n => axes (σ.assign n) (quota σ (σ.assign n) n)

/-- Even case: stage `2n` runs axis A at index `n`. -/
@[simp] theorem evenOdd_matches_fuseSteps_even
  (A B : Nat → Formula) (n : Nat) :
  scheduleSteps evenOddSchedule (evenOddAxes A B) (2*n) = A n := by
  unfold scheduleSteps
  simp only [evenOdd_assign_even, evenOddAxes_zero, quota_evenOdd_zero_even]

/-- Odd case: stage `2n+1` runs axis B at index `n`. -/
@[simp] theorem evenOdd_matches_fuseSteps_odd
  (A B : Nat → Formula) (n : Nat) :
  scheduleSteps evenOddSchedule (evenOddAxes A B) (2*n+1) = B n := by
  unfold scheduleSteps
  simp only [evenOdd_assign_odd, evenOddAxes_one, quota_evenOdd_one_odd]

private theorem twoDecomp (n : Nat) : ∃ m, n = 2*m ∨ n = 2*m + 1 := by
  -- We know n = (n/2)*2 + n%2 and n%2 < 2
  -- So either n%2 = 0 (even) or n%2 = 1 (odd)
  cases hm : n % 2 with
  | zero =>
      -- n is even: n = 2*(n/2)
      refine ⟨n / 2, ?_⟩
      left
      have : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
      rw [hm, Nat.add_zero] at this
      exact this.symm
  | succ k =>
      -- n%2 = k+1, but n%2 < 2, so k must be 0
      have : n % 2 < 2 := Nat.mod_lt n (by decide : 0 < 2)
      rw [hm] at this
      cases k with
      | zero =>
          -- n is odd: n = 2*(n/2) + 1
          refine ⟨n / 2, ?_⟩
          right
          have : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
          rw [hm] at this
          exact this.symm
      | succ k' =>
          -- impossible: Nat.succ (Nat.succ k') < 2
          contradiction

/-- Bridge theorem: The k=2 schedule (even/odd) exactly matches `fuseSteps`.
    This establishes that our general schedule framework correctly captures
    the existing fuseSteps construction for 2-axis products. -/
theorem evenOdd_is_fuseSteps
  {A B : Nat → Formula} (n : Nat) :
  scheduleSteps evenOddSchedule (evenOddAxes A B) n = fuseSteps A B n := by
  obtain ⟨m, hm | hm⟩ := twoDecomp n
  · -- even: n = 2*m
    rw [hm]
    simp [fuseSteps_even]
  · -- odd: n = 2*m + 1
    rw [hm]
    simp [fuseSteps_odd]

/-! ### Remaining k=2 closed-form quotas -/

/-- Quota for axis 0 at odd stages: ⌈(2n+1)/2⌉ = n+1. -/
@[simp] theorem quota_evenOdd_zero_odd (n : Nat) :
  quota evenOddSchedule (⟨0, by decide⟩ : Fin 2) (2*n+1) = n+1 := by
  -- Step from 2n to 2n+1: axis 0 fires at position 2n
  rw [quota_succ]
  rw [evenOdd_assign_even]
  rw [if_pos rfl]
  rw [quota_evenOdd_zero_even]

/-! ### k-ary round-robin bridge -/

/-- General k-ary decomposition: every n can be written as k*q + r with r < k. -/
theorem kDecomp (k : Nat) (hk : k > 0) (n : Nat) : 
  ∃ q r, n = k * q + r ∧ r < k :=
  ⟨n / k, n % k, (Nat.div_add_mod n k).symm, Nat.mod_lt n hk⟩

/-! ### k-ary round-robin: block structure and global bridge (Finset-free) -/

/-- On the block starting at `k*n`, time `k*n + r` (with `r < k`) selects axis `r`. -/
@[simp] theorem rr_assign_in_block (k n r : Nat) (hr : r < k) (hk : 0 < k) :
    (roundRobin k hk).assign (k*n + r) = ⟨r, hr⟩ := by
  apply Fin.ext
  simp [roundRobin, Nat.add_mod, Nat.mul_mod_right, Nat.mod_eq_of_lt hr]

/-- Arithmetic step for the "prefix count within a block". -/
private theorem step_if (a r : Nat) :
    (if a < r then 1 else 0) + (if a = r then 1 else 0)
      = (if a < r+1 then 1 else 0) := by
  classical
  by_cases hlt : a < r
  · have : a < r+1 := Nat.lt_trans hlt (Nat.lt_succ_self _)
    have ne : a ≠ r := fun h => (show False from Nat.lt_irrefl _ (h ▸ hlt))
    simp [hlt, ne, this]
  · by_cases heq : a = r
    · have : a < r+1 := by simp [heq]
      simp [heq]
    · have hge : r ≤ a := Nat.le_of_not_lt hlt
      have hgt : r < a := Nat.lt_of_le_of_ne hge (Ne.symm heq)
      have hnot : ¬ a < r+1 := Nat.not_lt.mpr (Nat.succ_le_of_lt hgt)
      simp [hlt, heq, hnot]

/-- Fold `quota_succ` across the first `r` steps of a block, measured from `k*n`. -/
private theorem rr_quota_prefix_rel (k : Nat) (hk : 0 < k) (i : Fin k) (n : Nat) :
    ∀ r, r ≤ k →
      quota (roundRobin k hk) i (k*n + r)
        = quota (roundRobin k hk) i (k*n) + (if i.val < r then 1 else 0)
  | 0, _ => by simp
  | r+1, hr => by
      have hr' : r < k := Nat.lt_of_succ_le hr
      have ih := rr_quota_prefix_rel k hk i n r (Nat.le_of_succ_le hr)
      have A : (roundRobin k hk).assign (k*n + r) = ⟨r, hr'⟩ :=
        rr_assign_in_block k n r hr' hk
      calc
        quota (roundRobin k hk) i (k*n + (r+1))
            = quota (roundRobin k hk) i ((k*n + r) + 1) := by
                simp [Nat.add_assoc]
        _   = quota (roundRobin k hk) i (k*n + r)
              + (if (roundRobin k hk).assign (k*n + r) = i then 1 else 0) := by
                exact quota_succ (σ := roundRobin k hk) (i := i) (m := k*n + r)
        _   = (quota (roundRobin k hk) i (k*n)
                + (if i.val < r then 1 else 0))
              + (if ⟨r, hr'⟩ = i then 1 else 0) := by
                simp [ih, A]
        _   = quota (roundRobin k hk) i (k*n)
              + ( (if i.val < r then 1 else 0)
                  + (if i.val = r then 1 else 0) ) := by
              -- turn equality of fins into equality of `val`
              have : ((⟨r, hr'⟩ : Fin k) = i) ↔ (r = i.val) := by
                constructor
                · intro h; exact congrArg Fin.val h
                · intro h; apply Fin.ext; simp [h]
              by_cases hrv : r = i.val
              · simp [hrv, Nat.add_comm]
              · have neg1 : ¬(i.val = r) := fun h => hrv h.symm
                have neg2 : ¬(⟨r, hr'⟩ : Fin k) = i := by
                  intro h; apply hrv; exact congrArg Fin.val h
                simp [neg1, neg2, Nat.add_comm]
        _   = quota (roundRobin k hk) i (k*n)
              + (if i.val < r+1 then 1 else 0) := by
              simp only [← step_if]

/-- Quota at block starts: after `k*n` steps, every axis has fired exactly `n` times. -/
@[simp] theorem rr_quota_at_block_start (k : Nat) (hk : 0 < k) (i : Fin k) :
    ∀ n, quota (roundRobin k hk) i (k*n) = n
  | 0 => by simp
  | n+1 => by
      have h := rr_quota_prefix_rel k hk i n k (Nat.le_refl k)
      have : (if i.val < k then 1 else 0) = 1 := by simp [i.isLt]
      rw [this, rr_quota_at_block_start k hk i n] at h
      -- Need to show: quota at k*(n+1) = n+1
      -- We have: quota at k*n + k = n + 1
      have eq : k * (n + 1) = k * n + k := by
        simp [Nat.mul_succ, Nat.add_comm]
      rw [eq]
      exact h

/-- Quota on your own axis inside the block: at `k*n + i.val` the local index is `n`. -/
@[simp] theorem rr_quota_on_axis_at_boundary (k : Nat) (hk : 0 < k) (i : Fin k) (n : Nat) :
    quota (roundRobin k hk) i (k*n + i.val) = n := by
  have h := rr_quota_prefix_rel k hk i n i.val (Nat.le_of_lt i.isLt)
  -- `i.val < i.val` is false
  simp only [rr_quota_at_block_start k hk i n, Nat.lt_irrefl, if_false, Nat.add_zero] at h
  exact h

/-- **Block bridge:** at stage `k*n + i.val`, round-robin runs axis `i` at local index `n`. -/
@[simp] theorem roundRobin_block_bridge
    {k : Nat} (hk : 0 < k) (axes : Fin k → Nat → Formula) (i : Fin k) (n : Nat) :
    scheduleSteps (roundRobin k hk) axes (k*n + i.val) = axes i n := by
  -- axis chosen:
  have A : (roundRobin k hk).assign (k*n + i.val) = i := by
    apply Fin.ext
    simp [roundRobin, Nat.add_mod, Nat.mul_mod_right, Nat.mod_eq_of_lt i.isLt]
  -- local index:
  have Q : quota (roundRobin k hk) i (k*n + i.val) = n :=
    rr_quota_on_axis_at_boundary k hk i n
  unfold scheduleSteps
  simp [A, Q]

/-- **Global bridge:** for any `n`, round-robin is exactly "remainder axis" with "block index".
    At stage `n` it runs axis `n % k` at local index `n / k`. -/
@[simp] theorem roundRobin_is_blocks
    {k : Nat} (hk : 0 < k) (axes : Fin k → Nat → Formula) (n : Nat) :
    scheduleSteps (roundRobin k hk) axes n
      = axes ⟨n % k, Nat.mod_lt n hk⟩ (n / k) := by
  -- We'll prove this using the decomposition n = k*(n/k) + n%k
  have hn : n = k*(n / k) + n % k := (Nat.div_add_mod n k).symm
  
  -- Now rewrite using the decomposition
  calc scheduleSteps (roundRobin k hk) axes n
      = scheduleSteps (roundRobin k hk) axes (k*(n/k) + n%k) := by rw [← hn]
    _ = axes ⟨n%k, Nat.mod_lt n hk⟩ (n/k) := by
        -- By roundRobin_block_bridge with i = ⟨n%k, _⟩
        -- Note: roundRobin_block_bridge takes i and yields axes i (n/k) at k*(n/k) + i.val
        -- Here i.val = n%k
        have eq_val : (⟨n%k, Nat.mod_lt n hk⟩ : Fin k).val = n%k := rfl
        have eq_rw : k*(n/k) + (⟨n%k, Nat.mod_lt n hk⟩ : Fin k).val = k*(n/k) + n%k := by
          rw [eq_val]
        rw [← eq_rw]
        exact roundRobin_block_bridge hk axes ⟨n%k, Nat.mod_lt n hk⟩ (n/k)

/-! ### Closed-form and global assignment for round-robin (Finset-free) -/

/-- Global assignment: round-robin picks the remainder axis. -/
@[simp] theorem roundRobin_assign (k : Nat) (hk : 0 < k) (n : Nat) :
    (roundRobin k hk).assign n = ⟨n % k, Nat.mod_lt n hk⟩ := by
  apply Fin.ext
  simp [roundRobin]

/-- **Closed form for quotas.** For round-robin on `k>0`,
    the quota on axis `i` after `n` steps is
    `n / k + (if i.val < n % k then 1 else 0)`. -/
@[simp] theorem quota_roundRobin_closed (k : Nat) (hk : 0 < k)
    (i : Fin k) (n : Nat) :
    quota (roundRobin k hk) i n
      = n / k + (if i.val < n % k then 1 else 0) := by
  -- decompose `n` into full blocks and remainder
  have hn : n = k * (n / k) + n % k := (Nat.div_add_mod n k).symm
  -- prefix relation inside the final block at base `k*(n/k)`
  have hprefix :=
    rr_quota_prefix_rel (k := k) (hk := hk) (i := i) (n := n / k)
                        (r := n % k) (Nat.le_of_lt (Nat.mod_lt n hk))
  -- base value at the block start
  have hbase := rr_quota_at_block_start (k := k) (hk := hk) (i := i) (n := n / k)
  
  
  -- assemble
  calc quota (roundRobin k hk) i n 
      = quota (roundRobin k hk) i (k * (n / k) + n % k) := by rw [← hn]
    _ = quota (roundRobin k hk) i (k * (n / k)) + (if i.val < n % k then 1 else 0) := hprefix
    _ = n / k + (if i.val < n % k then 1 else 0) := by rw [hbase]

/-! ### Handy 2-ary corollaries (even/odd) -/

-- Global assignment for k = 2
@[simp] theorem evenOdd_assign_global (n : Nat) :
    evenOddSchedule.assign n = ⟨n % 2, Nat.mod_lt n (by decide : 0 < 2)⟩ := by
  simp [evenOddSchedule, roundRobin_assign]

-- Closed form quotas for k = 2 (both axes, any `n`)
@[simp] theorem quota_evenOdd_closed_axis0 (n : Nat) :
    quota evenOddSchedule (⟨0, by decide⟩ : Fin 2) n
      = n / 2 + (if 0 < n % 2 then 1 else 0) := by
  simp [evenOddSchedule, quota_roundRobin_closed]

@[simp] theorem quota_evenOdd_closed_axis1 (n : Nat) :
    quota evenOddSchedule (⟨1, by decide⟩ : Fin 2) n
      = n / 2 + (if 1 < n % 2 then 1 else 0) := by
  simp [evenOddSchedule, quota_roundRobin_closed]

/-! ### Tiny "examples as tests" (compile-time checks) -/

-- Example: with k = 3, the 5th step hits axis 2.
example : (roundRobin 3 (by decide)).assign 5 = ⟨2, by decide⟩ := by
  simp [roundRobin_assign]

-- Example: with k = 3, axis 1 has quota 3 at time n = 8
-- (positions ≡ 1 mod 3 in {0,…,7} are 1,4,7).
example : quota (roundRobin 3 (by decide)) ⟨1, by decide⟩ 8 = 3 := by
  -- 8 / 3 = 2, 8 % 3 = 2, and 1 < 2 → +1
  simp [quota_roundRobin_closed]

/-! ## Convenience bridges for tests and rewrites -/

/-- Block start: at `k * n`, we are on axis `0` with local index `n`. -/
@[simp] theorem roundRobin_block_start_bridge
    {k : Nat} (hk : 0 < k) (axes : Fin k → Nat → Formula) (n : Nat) :
    scheduleSteps (roundRobin k hk) axes (k * n) = axes ⟨0, hk⟩ n := by
  -- From the global bridge with `m := k*n`
  simp [roundRobin_is_blocks, Nat.mul_mod_right, Nat.mul_div_right _ hk]

/-- k = 1 specialization: always axis `0`, local index = time. -/
@[simp] theorem roundRobin_k1_bridge (axes : Fin 1 → Nat → Formula) (n : Nat) :
    scheduleSteps (roundRobin 1 (by decide)) axes n = axes ⟨0, by decide⟩ n := by
  -- `n % 1 = 0`, `n / 1 = n`
  have h1 : n % 1 = 0 := Nat.mod_one n
  have h2 : n / 1 = n := Nat.div_one n
  simp [roundRobin_is_blocks, h1, h2]

/-! ### 2-ary (even/odd) wrappers -/

/-- Even/odd block start: at `2 * n`, axis `0`, local index `n`. -/
@[simp] theorem evenOdd_bridge_even (axes : Fin 2 → Nat → Formula) (n : Nat) :
    scheduleSteps evenOddSchedule axes (2 * n) = axes ⟨0, by decide⟩ n := by
  -- `2 * n = 2 * n + 0`, apply the block bridge with `i = 0`.
  simp only [evenOddSchedule]
  -- Use the already-proven roundRobin_block_start_bridge
  exact roundRobin_block_start_bridge (by decide : 0 < 2) axes n

/-- Even/odd offset: at `2 * n + 1`, axis `1`, local index `n`. -/
@[simp] theorem evenOdd_bridge_odd (axes : Fin 2 → Nat → Formula) (n : Nat) :
    scheduleSteps evenOddSchedule axes (2 * n + 1) = axes ⟨1, by decide⟩ n := by
  -- This is exactly the block bridge with `i = 1` (since `i.val = 1`).
  simp only [evenOddSchedule]
  -- Now we have scheduleSteps (roundRobin 2 _) axes (2 * n + 1)
  -- We need to use the general roundRobin_block_bridge theorem
  have := @roundRobin_block_bridge 2 (by decide : 0 < 2) axes ⟨1, by decide⟩ n
  -- roundRobin_block_bridge says: scheduleSteps ... (k*n + i.val) = axes i n
  -- With k=2, i=1, this gives: scheduleSteps ... (2*n + 1) = axes ⟨1,_⟩ n
  exact this

/-! ### Closed-form helpers (k = 2) -/

-- Note: The cleaner forms (n+1)/2 and n/2 require more complex proofs
-- involving the identity (n+1)/2 = n/2 + n%2, which needs careful case analysis.
-- For now we keep the original forms with the indicator functions,
-- which are still quite usable in practice.

/-! ### Equivalence between evenOddSchedule and fuseSteps -/

/-- On even stages, `evenOddSchedule` and `fuseSteps` agree. -/
@[simp] theorem evenOdd_eq_fuseSteps_even
    (A B : Nat → Formula) (n : Nat) :
  scheduleSteps evenOddSchedule (fun i => if i = 0 then A else B) (2 * n)
    = fuseSteps A B (2 * n) := by
  -- left side picks axis 0 at local index n
  -- right side is `fuseSteps_even`
  simp [evenOdd_bridge_even, fuseSteps_even]

/-- On odd stages, `evenOddSchedule` and `fuseSteps` agree. -/
@[simp] theorem evenOdd_eq_fuseSteps_odd
    (A B : Nat → Formula) (n : Nat) :
  scheduleSteps evenOddSchedule (fun i => if i = 0 then A else B) (2 * n + 1)
    = fuseSteps A B (2 * n + 1) := by
  -- left side picks axis 1 at local index n
  -- right side is `fuseSteps_odd`
  simp [evenOdd_bridge_odd, fuseSteps_odd]

/-! ## Part 6: Block-closed quotas & target characterization

These theorems characterize exactly when a k-ary product reaches target heights,
enabling sharp finish-time results and generalizing the binary product height theorems.
-/

/-- Closed form *inside a block*: at time `k*n + r` (with `r ≤ k`),
    the quota for axis `i` is `n + (if i.val < r then 1 else 0)`. -/
@[simp] theorem quota_roundRobin_block_closed
    (k : Nat) (hk : 0 < k) (i : Fin k) (n r : Nat) (hr : r ≤ k) :
  quota (roundRobin k hk) i (k*n + r)
    = n + (if i.val < r then 1 else 0) := by
  -- Use rr_quota_prefix_rel and the fact that quota at block start is n
  have h1 := rr_quota_prefix_rel k hk i n r hr
  have h2 := rr_quota_at_block_start k hk i n
  simp only [h2] at h1
  exact h1

/-- **Target characterization at time `n`.**
    Rewrites feasibility at time n to a closed-form inequality in n / k and n % k.
    Writing `n = k*(n/k) + n%k`, quotas meet targets `q` iff
    each `q i` fits into the `(n/k)` full cycles plus the 1-step prefix of length `n%k`. -/
theorem quotas_reach_targets_iff
    (k : Nat) (hk : 0 < k) (q : Fin k → Nat) (n : Nat) :
  (∀ i, q i ≤ quota (roundRobin k hk) i n)
    ↔ (∀ i, q i ≤ n / k + (if i.val < n % k then 1 else 0)) := by
  -- Use the global closed form of quotas already proved.
  simp only [quota_roundRobin_closed]

-- Note: A full monotonicity proof for quotas would require careful case analysis
-- on the relationship between a%k and b%k. For now we focus on the key
-- characterization theorems which are sufficient for the finish-time results.

/-! ### Exact Finish Time Characterization

The minimal time N* to reach target heights h : Fin k → ℕ has a clean closed form:
- Let H = max_i h(i) and S = #{i : h(i) = H} (the number of maximal axes)
- If we can reindex axes (symmetric product), then:
  * N* = 0 if H = 0
  * N* = k(H-1) + S if 1 ≤ S ≤ k-1
  * N* = kH if S = k
  
This generalizes the binary case where:
- If the unique max is on axis 0, we finish at 2H-1
- If the unique max is on axis 1, we need 2H

The proof strategy:
1. Upper bound: Show quotas reach targets at N* by placing maximal axes first
2. Lower bound: Show any n < N* leaves at least one maximal axis short
-/

/-- **Packed achievability (reindexed, Finset-free).**
If the axes with maximal demand `H` are exactly the first `S` indices (after reindexing),
then at time `k*(H-1) + S` all targets are met. The case `H = 0` is trivial (time `0`). -/
theorem quotas_reach_targets_packed
    (k : Nat) (hk : 0 < k) (h : Fin k → Nat)
    (H S : Nat) (hS : S ≤ k)
    (bound : ∀ i, h i ≤ H)
    (pack  : ∀ i, (h i = H) ↔ i.val < S) :
  (∀ i, h i ≤ quota (roundRobin k hk) i (k * (H - 1) + S)) := by
  intro i
  -- Closed form inside the block whose index is (H-1) and offset S
  have hquota :
      quota (roundRobin k hk) i (k * (H - 1) + S)
        = (H - 1) + (if i.val < S then 1 else 0) :=
    quota_roundRobin_block_closed (k := k) (hk := hk) (i := i) (n := H - 1) (r := S) hS
  -- Is `i` one of the S maximal-demand axes?
  by_cases hi : i.val < S
  · -- Maximal axis: needs `H`, quota gives `(H-1)+1 = H`.
    have hi_eq : h i = H := (pack i).mpr hi
    rw [hquota, hi_eq]
    simp only [hi, if_true]
    -- Need to handle the case where H = 0 separately
    by_cases hH : H = 0
    · simp [hH]
    · have : H - 1 + 1 = H := Nat.sub_add_cancel (Nat.pos_of_ne_zero hH)
      rw [this]
      -- Goal is now H ≤ H which is trivial
      exact Nat.le_refl H
  · -- Non-max axis: `h i ≤ H-1`.
    have hi_ne : h i ≠ H := by
      intro hEq; exact hi ((pack i).mp hEq)
    have hi_ltH : h i < H := Nat.lt_of_le_of_ne (bound i) hi_ne
    -- For H > 0, we have h i ≤ H - 1
    by_cases hH : H = 0
    · -- If H = 0, then h i = 0 (since h i ≤ H = 0)
      have hbound : h i ≤ 0 := by rw [← hH]; exact bound i
      have : h i = 0 := Nat.eq_zero_of_le_zero hbound
      simp [hquota, hi, this]
    · -- H > 0, so h i < H implies h i ≤ H - 1
      have hi_le : h i ≤ H - 1 := Nat.le_pred_of_lt hi_ltH
      -- quota gives `(H-1)+0 = H-1`
      rw [hquota]
      simp [hi]
      exact hi_le

end Papers.P4Meta