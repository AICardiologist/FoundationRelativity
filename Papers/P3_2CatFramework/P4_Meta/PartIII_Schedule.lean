/-
  Papers/P3_2CatFramework/P4_Meta/PartIII_Schedule.lean
  
  Schedule and quota invariants for k-ary proof height calculus.
  This generalizes the parity obstruction used in 2-axis case to
  arbitrary periodic schedules.
-/
import Papers.P3_2CatFramework.P4_Meta.PartIII_ProductHeight
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Fin
import Mathlib.Logic.Basic

namespace Papers.P4Meta

open Finset

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

/-! ### Part 6B: Packed lower bound (Finset-free)

This proves that any time strictly below k*(H-1) + S leaves at least one maximal axis short.
The proof is constructive and elementary, avoiding Finset entirely.
-/

/-! ### Tiny arithmetic helpers for Part 6 -/

@[simp] lemma sub_one_lt_self {H : Nat} (hH : 0 < H) : H - 1 < H := by
  -- `Nat.pred H < H`, and `Nat.pred H = H - 1`
  simpa [Nat.pred] using Nat.pred_lt (Nat.ne_of_gt hH)

lemma k_mul_pred_succ (k H : Nat) (hH : 0 < H) :
    k * H = k * (H - 1) + k := by
  -- Use the fact that H = (H-1) + 1 when H > 0
  conv_lhs => rw [← Nat.succ_pred_eq_of_pos hH]
  rw [Nat.pred_eq_sub_one, Nat.succ_eq_add_one, Nat.mul_add]
  simp [Nat.mul_one]

/-- **Packed lower bound (constructive, Finset-free).**
If the axes with maximal demand `H` are exactly the first `S` indices (after reindexing),
and `0 < H` and `0 < S`, then for any `n < k*(H-1) + S` there exists a maximal axis
whose quota is still `< H`. -/
theorem quotas_not_reached_below_packed
    (k : Nat) (hk : 0 < k) (h : Fin k → Nat)
    (H S : Nat) (hH : 0 < H) (hS : S ≤ k) (hSpos : 0 < S)
    (bound : ∀ i, h i ≤ H)
    (pack : ∀ i, (h i = H) ↔ i.val < S) :
  ∀ {n}, n < k * (H - 1) + S →
    ∃ i, h i = H ∧ quota (roundRobin k hk) i n < H := by
  intro n hn
  -- decompose n
  obtain ⟨m, r, rfl, hr⟩ := kDecomp k hk n
  by_cases hm : m < H - 1
  · -- Case A: `m < H-1`
    have hk0 : 0 < k := Nat.lt_of_lt_of_le hSpos hS
    refine ⟨⟨0, hk0⟩, ?_, ?_⟩
    · exact (pack ⟨0, hk0⟩).mpr hSpos
    · have hq :=
        quota_roundRobin_block_closed k hk ⟨0, hk0⟩ m r (Nat.le_of_lt hr)
      by_cases h0r : (0 : Nat) < r
      · -- quota = m+1 ≤ H-1 < H
        simp [hq, h0r]
        have : m + 1 ≤ H - 1 := Nat.succ_le_of_lt hm
        exact Nat.lt_of_le_of_lt this (by
          -- `H-1 < H` since `H>0`
          exact sub_one_lt_self hH)
      · -- quota = m < H
        simp [hq, h0r]
        exact Nat.lt_trans hm (by
          -- `H-1 < H`
          exact sub_one_lt_self hH)
  · -- Case B: `H-1 ≤ m`
    have hm' : H - 1 ≤ m := Nat.le_of_not_gt hm
    -- First show `m < H`, otherwise we contradict `hn`
    have m_lt_H : m < H := by
      -- If `H ≤ m`, then `k*(H-1)+S ≤ k*H ≤ k*m ≤ k*m + r`, contradicting `hn`
      by_contra hge
      have H_le_m : H ≤ m := Nat.le_of_not_gt hge
      -- `k*H = k*(H-1) + k`
      have kH_eq : k * H = k * (H - 1) + k := k_mul_pred_succ k H hH
      have kH_ge_target : k * (H - 1) + S ≤ k * H := by
        -- `S ≤ k` ⇒ `k*(H-1)+S ≤ k*(H-1)+k = k*H`
        simpa [kH_eq] using Nat.add_le_add_left hS (k * (H - 1))
      have kH_le_km : k * H ≤ k * m := Nat.mul_le_mul_left _ H_le_m
      have : k * (H - 1) + S ≤ k * m + r :=
        Nat.le_trans (Nat.le_trans kH_ge_target kH_le_km) (Nat.le_add_right _ _)
      exact (Nat.not_lt_of_ge this) hn
    -- So `H-1 ≤ m < H`, hence `m = H-1`
    have hm_eq : m = H - 1 := by
      have : m ≤ H - 1 := by
        have hEq := Nat.succ_pred_eq_of_pos hH
        -- `m < H = (H-1).succ` ⇒ `m ≤ H-1`
        rw [← hEq] at m_lt_H
        exact Nat.lt_succ_iff.mp m_lt_H
      exact Nat.le_antisymm this hm'
    -- From `n < k*(H-1)+S` and `m = H-1` we get `r < S`
    have hrS : r < S := by
      have : k * (H - 1) + r < k * (H - 1) + S := by simpa [hm_eq] using hn
      exact Nat.lt_of_add_lt_add_left this
    have hrk : r < k := Nat.lt_of_lt_of_le hrS hS
    refine ⟨⟨r, hrk⟩, ?_, ?_⟩
    · exact (pack ⟨r, hrk⟩).mpr hrS
    · -- quota at `k*(H-1) + r` is exactly `H-1`
      have hq :=
        quota_roundRobin_block_closed k hk ⟨r, hrk⟩ (H - 1) r (Nat.le_of_lt hrk)
      -- the indicator `r < r` is false
      -- First rewrite the LHS to `H - 1`, then close with `H - 1 < H`.
      have qeq :
          quota (roundRobin k hk) ⟨r, hrk⟩ (k * (H - 1) + r) = H - 1 := by
        -- the "+ if (r<r) then 1 else 0" collapses to +0
        simpa [hq, Nat.lt_irrefl]
      -- now the goal is quota (roundRobin k hk) ⟨r, hrk⟩ (k*m + r) < H
      -- We have m = H - 1, so k*m + r = k*(H-1) + r
      rw [hm_eq, qeq]
      exact sub_one_lt_self hH

/-! ### Part 6C: Exact Finish Time Characterization

Now we combine the upper and lower bounds to get the exact characterization
of the finish time in the packed case.
-/

/-- The exact finish time formula for reaching target heights.
    When H = 0, we finish immediately. Otherwise we need k*(H-1) + S steps. -/
def Nstar (k H S : Nat) : Nat := 
  if H = 0 then 0 else k * (H - 1) + S

/-! ### `Nstar` utilities -/

@[simp] lemma Nstar_zero (k S : Nat) : Nstar k 0 S = 0 := by
  simp [Nstar]

@[simp] lemma Nstar_succ (k H S : Nat) : Nstar k (H.succ) S = k * H + S := by
  simp [Nstar]

lemma lt_Nstar_iff_of_posH {k H S n : Nat} (hH : 0 < H) :
    n < Nstar k H S ↔ n < k * (H - 1) + S := by
  have : H ≠ 0 := Nat.ne_of_gt hH
  simp [Nstar, this]

lemma Nstar_le_iff_of_posH {k H S n : Nat} (hH : 0 < H) :
    Nstar k H S ≤ n ↔ k * (H - 1) + S ≤ n := by
  have : H ≠ 0 := Nat.ne_of_gt hH
  simp [Nstar, this]

lemma Nstar_mono_S {k H S S' : Nat} (hSS' : S ≤ S') :
    Nstar k H S ≤ Nstar k H S' := by
  by_cases hH0 : H = 0
  · simp [Nstar, hH0]
  · have : H ≠ 0 := hH0
    have : 0 < H := Nat.pos_of_ne_zero hH0
    -- both sides take the `H>0` branch
    simpa [Nstar, (ne_of_gt this)] using Nat.add_le_add_left hSS' (k * (H - 1))

lemma Nstar_mono_k {k k' H S : Nat} (hk : k ≤ k') (hH : 0 < H) :
    Nstar k H S ≤ Nstar k' H S := by
  have hHne : H ≠ 0 := Nat.ne_of_gt hH
  have hk' : k * (H - 1) ≤ k' * (H - 1) := Nat.mul_le_mul_right _ hk
  simpa [Nstar, hHne] using Nat.add_le_add_right hk' S

/-- Nstar is strictly monotone in k when H > 1. -/
lemma Nstar_strict_mono_k {k k' H S : Nat} (hk : k < k') (hH : 1 < H) :
    Nstar k H S < Nstar k' H S := by
  have hHne : H ≠ 0 := Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one hH)
  have h_pos : 0 < H - 1 := Nat.sub_pos_of_lt hH
  have hk' : k * (H - 1) < k' * (H - 1) :=
    Nat.mul_lt_mul_of_pos_right hk h_pos
  simpa [Nstar, hHne] using Nat.add_lt_add_right hk' S

/-- Lower bound: when `H>0`, `N*` is at least `k*(H-1)`. -/
lemma Nstar_lower_bound {k H S : Nat} (hH : 0 < H) :
    k * (H - 1) ≤ Nstar k H S := by
  have hHne : H ≠ 0 := Nat.ne_of_gt hH
  -- `k*(H-1) ≤ k*(H-1)+S`
  have := Nat.le_add_right (k * (H - 1)) S
  simpa [Nstar, hHne] using this

/-- Upper bound: `N* ≤ k*H` when `S ≤ k`. -/
lemma Nstar_upper_bound {k H S : Nat} (hS : S ≤ k) :
    Nstar k H S ≤ k * H := by
  by_cases hH0 : H = 0
  · simp [Nstar, hH0]
  · have hH : 0 < H := Nat.pos_of_ne_zero hH0
    -- `k*(H-1)+S ≤ k*(H-1)+k = k*H`
    have step : k * (H - 1) + S ≤ k * (H - 1) + k :=
      Nat.add_le_add_left hS _
    -- Need to show k * (H - 1) + k = k * H
    have eq : k * (H - 1) + k = k * H := by
      rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.one_le_of_lt hH)]
    rw [eq] at step
    simpa [Nstar, (ne_of_gt hH)] using step

/-! ### Packed profile (one place for the hypotheses you already use) -/

structure PackedProfile (k : Nat) (h : Fin k → Nat) (H S : Nat) : Prop where
  (hS_le  : S ≤ k)
  (bound  : ∀ i, h i ≤ H)
  (pack   : ∀ i, (h i = H) ↔ i.val < S)
  (attain : H = 0 ∨ ∃ i, h i = H)

namespace PackedProfile
  variable {k H S} {h : Fin k → Nat}

  /-- From `H>0` and `attain`, packedness forces `S>0`. -/
  lemma s_pos_of_posH (pp : PackedProfile k h H S) (hH : 0 < H) : 0 < S := by
    -- If `H>0`, there exists `i` with `h i = H`; then `(pp.pack i)` gives `i.val < S`.
    have hHne : H ≠ 0 := Nat.ne_of_gt hH
    rcases pp.attain with h0 | ⟨i, hi⟩
    · cases hHne h0
    · have : i.val < S := (pp.pack i).mp hi
      exact Nat.lt_of_le_of_lt (Nat.zero_le _) this

  /-- If `S = 0`, packedness + attain forces `H = 0`.
      (Only this direction is valid; the converse need not hold.) -/
  lemma h_zero_of_s_zero (pp : PackedProfile k h H S) (hS0 : S = 0) : H = 0 := by
    rcases pp.attain with h0 | ⟨i, hi⟩
    · exact h0
    · have : i.val < S := (pp.pack i).mp hi
      have : False := by simpa [hS0] using this
      exact this.elim

  /-- A simp‑friendly orientation of `pack`. -/
  @[simp] lemma lt_iff_max (pp : PackedProfile k h H S) (i : Fin k) :
      i.val < S ↔ h i = H :=
    (pp.pack i).symm
end PackedProfile

/-- Quotas are monotone in time: if `a ≤ b` then `quota σ i a ≤ quota σ i b`. -/
theorem quota_mono {k} (σ : Schedule k) (i : Fin k) :
  ∀ {a b}, a ≤ b → quota σ i a ≤ quota σ i b := by
  intro a b h
  -- write b = a + d
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  -- goal: quota σ i a ≤ quota σ i (a + d)
  induction d with
  | zero =>
      simpa
  | succ d ih =>
      -- show a single step is monotone, then chain with `ih`
      have step : quota σ i (a + d) ≤ quota σ i (a + (d + 1)) := by
        -- First normalize a + (d + 1) to (a + d) + 1
        have eq : a + (d + 1) = (a + d) + 1 := by simp [Nat.add_assoc]
        rw [eq]
        have hq := quota_succ σ i (a + d)
        by_cases h : σ.assign (a + d) = i
        · -- RHS = quota + 1; `x ≤ x+1`
          rw [hq, if_pos h]
          exact Nat.le_succ (quota σ i (a + d))
        · -- RHS = quota + 0 = quota; `x ≤ x`
          rw [hq, if_neg h, Nat.add_zero]
      exact Nat.le_trans ih step

/-- Quotas are monotone in `n` (function view). -/
lemma quota_monotone {k} (σ : Schedule k) (i : Fin k) :
    Monotone (fun n => quota σ i n) := by
  intro a b hab; exact quota_mono σ i hab

/-- All targets `h` are met by time `n` for schedule `σ`. -/
def targetsMet {k} (σ : Schedule k) (h : Fin k → Nat) (n : Nat) : Prop :=
  ∀ i, h i ≤ quota σ i n

/-- If time increases, once all targets are met they stay met. -/
lemma targetsMet_mono {k} (σ : Schedule k) (h : Fin k → Nat) :
    Monotone (fun n => targetsMet σ h n) := by
  intro a b hab hall i
  exact Nat.le_trans (hall i) (quota_mono σ i hab)

/-- **Exact finish time (packed case).**
For axes reindexed so that the first S have maximal demand H, quotas reach all targets
if and only if n ≥ N* = k*(H-1) + S (or N* = 0 when H = 0).
Note: When H > 0, we require S > 0 (some axis actually attains the maximum). -/
theorem quotas_targets_exact_packed
    (k : Nat) (hk : 0 < k) (h : Fin k → Nat)
    (H S : Nat) (hS : S ≤ k)
    (bound : ∀ i, h i ≤ H)
    (pack : ∀ i, (h i = H) ↔ i.val < S)
    (hmax_attained : H = 0 ∨ ∃ i, h i = H) :
  ∀ n, (∀ i, h i ≤ quota (roundRobin k hk) i n) ↔ Nstar k H S ≤ n := by
  intro n; unfold Nstar
  by_cases hH0 : H = 0
  · -- trivial 0-target case
    constructor
    · intro _
      simp [hH0]
    · intro _ i
      have : h i ≤ 0 := by simpa [hH0] using bound i
      have hi0 : h i = 0 := Nat.eq_zero_of_le_zero this
      simpa [hH0, hi0] using (Nat.zero_le (quota (roundRobin k hk) i n))
  · -- main case: H > 0, and in packed form we also need S > 0
    have hH : 0 < H := Nat.pos_of_ne_zero hH0
    have hSpos : 0 < S := by
      -- In packed form with H > 0, we need S > 0 for well-formedness
      -- If S = 0, then by pack: (h i = H) ↔ (i.val < 0) ↔ False
      -- So no axis would have h i = H. But H is the supremum of h values,
      -- and with bound saying all h i ≤ H, at least one must equal H.
      -- We assert this as a well-formedness requirement.
      by_contra hS0
      have hS_eq : S = 0 := Nat.eq_zero_of_not_pos hS0
      -- Since S = 0, pack says no axis has demand H
      have no_max : ∀ i, h i < H := by
        intro i
        have : h i ≠ H := by
          intro hi_eq
          have : i.val < S := (pack i).mp hi_eq
          rw [hS_eq] at this
          exact Nat.not_lt_zero _ this
        exact Nat.lt_of_le_of_ne (bound i) this
      -- But hmax_attained says H = 0 ∨ ∃ i, h i = H
      cases hmax_attained with
      | inl h0 => exact (hH0 h0).elim
      | inr hex => 
        obtain ⟨i, hi⟩ := hex
        have : h i < H := no_max i
        rw [hi] at this
        exact Nat.lt_irrefl H this
    -- `Nstar` simplifies
    simp [hH0]
    constructor
    · -- forward: if all targets met at n, then n ≥ k*(H-1)+S (contradict lower bound)
      intro hall
      by_contra hn
      have hn' : n < k * (H - 1) + S := Nat.not_le.mp hn
      have ⟨i, hiH, hiShort⟩ :=
        quotas_not_reached_below_packed k hk h H S hH hS hSpos bound pack hn'
      have : h i ≤ quota (roundRobin k hk) i n := by
        have eq := quota_roundRobin_closed k hk i n
        rw [eq]
        exact hall i
      -- contradiction: quota i n < H but h i = H
      rw [hiH] at this
      exact absurd this (Nat.not_le_of_lt hiShort)
    · -- backward: lift the upper bound by monotonicity
      intro hN i
      have base := quotas_reach_targets_packed k hk h H S hS bound pack i
      -- base says: h i ≤ quota (roundRobin k hk) i (k * (H - 1) + S)
      -- We need: h i ≤ quota (roundRobin k hk) i n
      -- Since n ≥ k * (H - 1) + S, monotonicity gives us what we need
      rw [← quota_roundRobin_closed k hk i n]
      exact Nat.le_trans base (quota_mono (roundRobin k hk) i hN)


/-! ### Clean API wrappers (packed lower bound and exactness) -/

/-- **Packed lower bound (API).**
If the profile is packed and `H>0`, then for any `n < N*` some maximal axis is still short. -/
theorem quotas_not_reached_below_packed_of
    {k : Nat} (hk : 0 < k) {h : Fin k → Nat} {H S : Nat}
    (pp : PackedProfile k h H S) (hH : 0 < H) :
    ∀ {n}, n < Nstar k H S →
      ∃ i, h i = H ∧ quota (roundRobin k hk) i n < H := by
  intro n hn
  have hSpos : 0 < S := PackedProfile.s_pos_of_posH pp hH
  -- `Nstar` reduces to `k*(H-1)+S` when `H>0`:
  have hNstar : Nstar k H S = k * (H - 1) + S := by
    simp [Nstar, (ne_of_gt hH)]
  -- rewrite the hypothesis using this fact
  rw [hNstar] at hn
  -- hand the work to your finished lemma
  exact quotas_not_reached_below_packed k hk h H S hH pp.hS_le hSpos pp.bound pp.pack hn

/-- **Exact finish time (packed case, API).**
All targets are met at time `n` iff `N* ≤ n`, packaged in one hypothesis. -/
theorem quotas_targets_exact_packed_of
    {k : Nat} (hk : 0 < k) {h : Fin k → Nat} {H S : Nat}
    (pp : PackedProfile k h H S) :
    ∀ n, (∀ i, h i ≤ quota (roundRobin k hk) i n) ↔ Nstar k H S ≤ n := by
  intro n
  -- Directly reuse your completed exactness theorem.
  exact quotas_targets_exact_packed k hk h H S pp.hS_le pp.bound pp.pack pp.attain n

/-- Packed case (API with `targetsMet`). -/
theorem targetsMet_iff_ge_Nstar_packed
    {k : Nat} (hk : 0 < k) {h : Fin k → Nat} {H S : Nat}
    (pp : PackedProfile k h H S) :
    ∀ n, targetsMet (roundRobin k hk) h n ↔ Nstar k H S ≤ n := by
  intro n
  simpa [targetsMet] using
    quotas_targets_exact_packed_of (k := k) (hk := hk) (h := h) (H := H) (S := S) pp n

/-- Corollary: at `N*` itself the packed profile is met (H>0 branch handled by `Nstar`). -/
theorem targetsMet_at_Nstar_packed
    {k : Nat} (hk : 0 < k) {h : Fin k → Nat} {H S : Nat}
    (pp : PackedProfile k h H S) :
    targetsMet (roundRobin k hk) h (Nstar k H S) := by
  have := targetsMet_iff_ge_Nstar_packed (k := k) hk (h := h) (H := H) (S := S) pp (Nstar k H S)
  -- `Nstar ≤ Nstar`
  simpa using (this.mpr (Nat.le_refl _))

/-- If `h₁ ≤ h₂` pointwise, any time that meets `h₂` also meets `h₁`. -/
lemma targetsMet_antitone_targets {k}
    (σ : Schedule k) {h₁ h₂ : Fin k → Nat}
    (hle : ∀ i, h₁ i ≤ h₂ i) :
    ∀ {n}, targetsMet σ h₂ n → targetsMet σ h₁ n := by
  intro n hall i
  exact Nat.le_trans (hle i) (hall i)

/-- A convenient dual form: failing to meet all targets at time `n`
    is the same as having at least one axis still short. -/
lemma not_targetsMet_iff_exists_short {k}
    (σ : Schedule k) (h : Fin k → Nat) (n : Nat) :
    (¬ targetsMet σ h n) ↔ ∃ i, h i > quota σ i n := by
  classical
  unfold targetsMet
  constructor
  · intro hnot
    -- `¬ ∀ i, h i ≤ quota σ i n` → `∃ i, ¬ h i ≤ quota σ i n`
    rcases (not_forall).1 hnot with ⟨i, hi⟩
    -- `¬ a ≤ b` on `Nat` is `b < a`
    exact ⟨i, Nat.lt_of_not_ge hi⟩
  · rintro ⟨i, hi⟩ hall
    -- contradiction with `h i ≤ quota σ i n`
    exact (Nat.not_le.mpr hi) (hall i)

/-- **Packed lower bound (targetsMet view).**
    If the profile is packed and `H>0`, then for any `n < N*` the packed targets
    cannot be met at time `n`. -/
theorem not_targetsMet_below_Nstar_packed_of
    {k : Nat} (hk : 0 < k) {h : Fin k → Nat} {H S : Nat}
    (pp : PackedProfile k h H S) (hH : 0 < H) :
    ∀ {n}, n < Nstar k H S →
      ¬ targetsMet (roundRobin k hk) h n := by
  intro n hn
  -- your existing witness lemma
  obtain ⟨i, hiH, hiShort⟩ :=
    quotas_not_reached_below_packed_of (k := k) hk (h := h) (H := H) (S := S) pp hH hn
  -- rewrite the strict inequality with `targetsMet` negation
  have hex : ∃ j, h j > quota (roundRobin k hk) j n := ⟨i, by simpa [hiH] using hiShort⟩
  simpa [not_targetsMet_iff_exists_short (roundRobin k hk) h n] using hex

/-! ## Part 6C-D: General Case via Permutation

The general case reduces to the packed case by permuting axes to pack
maximal elements first. The finish time is invariant under such permutations.
-/

/-! ### Permutation machinery -/

/-- Permute axis labels of a schedule by `π`.
    `assign n` says "who gets the (n)th tick." After permutation, the label that used
    to be `π j` becomes `j`. Using `π.symm` here makes the main lemmas come out
    with clean right-hand sides. -/
def permuteSchedule {k : Nat} (π : Equiv (Fin k) (Fin k)) (τ : Schedule k) : Schedule k :=
  { assign := fun n => π.symm (τ.assign n) }

private lemma permute_assign_eq_iff {k} (π : Equiv (Fin k) (Fin k))
    (τ : Schedule k) (n : Nat) (j : Fin k) :
    (permuteSchedule π τ).assign n = j ↔ τ.assign n = π j := by
  -- π.symm a = j  ↔  a = π j
  unfold permuteSchedule
  constructor
  · intro h
    -- π.symm a = j implies a = π j
    have : π (π.symm (τ.assign n)) = π j := congrArg π h
    simpa using this
  · intro h
    -- a = π j implies π.symm a = j
    have : π.symm (τ.assign n) = π.symm (π j) := congrArg π.symm h
    simpa using this

/-- Quotas are carried through a permutation of axis labels. -/
lemma quota_perm {k} (π : Equiv (Fin k) (Fin k))
    (τ : Schedule k) (j : Fin k) :
    ∀ n, quota (permuteSchedule π τ) j n = quota τ (π j) n := by
  intro n; induction n with
  | zero => rfl
  | succ n ih =>
    -- one-step expansions
    have hL := quota_succ (permuteSchedule π τ) j n
    have hR := quota_succ τ (π j) n
    -- line up the "who fires at step n?" tests
    have hiff := permute_assign_eq_iff (π := π) (τ := τ) (n := n) (j := j)
    by_cases h : (permuteSchedule π τ).assign n = j
    · have h' : τ.assign n = π j := (hiff.mp h)
      -- both sides add 1 in this step
      simpa [hL, hR, ih, h, h', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    · have h' : τ.assign n ≠ π j := by
        intro hEq; exact h (hiff.mpr hEq)
      -- neither side adds 1 in this step
      simpa [hL, hR, ih, h, h', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Meeting targets after permuting axes is the same as meeting the
    correspondingly permuted target vector on the original schedule. -/
lemma targetsMet_permute {k}
    (π : Equiv (Fin k) (Fin k)) (τ : Schedule k) (h : Fin k → Nat) (n : Nat) :
    targetsMet (permuteSchedule π τ) h n
      ↔ targetsMet τ (fun i => h (π.symm i)) n := by
  -- unfold once and shuttle inequalities along `quota_perm`
  unfold targetsMet
  constructor
  · intro hall i
    -- pick j with i = π j  (namely j = π.symm i)
    have := hall (π.symm i)
    -- rewrite quotas via quota_perm and π.symm_apply_apply
    simpa [quota_perm (π := π) (τ := τ), Equiv.apply_symm_apply] using this
  · intro hall j
    -- set i = π j
    have := hall (π j)
    -- rewrite back the other way
    simpa [quota_perm (π := π) (τ := τ), Equiv.symm_apply_apply] using this

/-! ### General case via packing specification -/

/-- `IsPacking k h π H S` says: the permutation `π` puts exactly the `H`-level
    axes in the first `S` slots, and the rest below `H`. This is the right notion
    to feed your packed theorems without committing to any particular construction
    of `π`. -/
structure IsPacking (k : Nat) (h : Fin k → Nat)
    (π : Equiv (Fin k) (Fin k)) (H S : Nat) : Prop :=
  (hS_le  : S ≤ k)
  (bound  : ∀ i, h i ≤ H)
  (block  : ∀ j, (h (π.symm j) = H) ↔ j.val < S)
  (attain : H = 0 ∨ ∃ i, h i = H)

namespace IsPacking
  variable {k : Nat} {h : Fin k → Nat} {π : Equiv (Fin k) (Fin k)} {H S : Nat}

/-- Any `IsPacking` instance yields a packed profile for the permuted targets
    `i ↦ h (π.symm i)`. -/
def toPackedProfile (ip : IsPacking k h π H S) :
    PackedProfile k (fun i => h (π.symm i)) H S :=
{ hS_le  := ip.hS_le
, bound  := fun i => ip.bound (π.symm i)
, pack   := fun i => ip.block i
, attain := by
    cases ip.attain with
    | inl h0 => left; exact h0
    | inr hex =>
      right
      obtain ⟨i, hi⟩ := hex
      -- We need to show ∃ j, h (π.symm j) = H
      -- Take j = π i, then π.symm (π i) = i
      use π i
      simpa using hi
}

  /-- From `H > 0` and `attain`, packing forces `0 < S`. -/
  lemma s_pos_of_posH (ip : IsPacking k h π H S) (hH : 0 < H) : 0 < S := by
    -- `attain` gives us a witness `i` with `h i = H` (since `H ≠ 0`)
    have hHne : H ≠ 0 := Nat.ne_of_gt hH
    rcases ip.attain with h0 | ⟨i, hi⟩
    · cases hHne h0
    · -- choose `j := π i`; then `h (π.symm j) = h i = H` so `j.val < S` by `block`
      have j_lt_S : (π i).val < S := by
        have hmax : h (π.symm (π i)) = H := by simpa using hi
        exact (ip.block (π i)).mp hmax
      exact Nat.lt_of_le_of_lt (Nat.zero_le _) j_lt_S

  /-- A simp‑friendly orientation of the block condition. -/
  @[simp] lemma block_iff (ip : IsPacking k h π H S) (j : Fin k) :
      (h (π.symm j) = H) ↔ j.val < S :=
    ip.block j

  /-- The converse orientation, also simp‑friendly. -/
  @[simp] lemma lt_iff_max (ip : IsPacking k h π H S) (j : Fin k) :
      j.val < S ↔ (h (π.symm j) = H) :=
    (ip.block j).symm

end IsPacking

/-- **General exact time via permutation.**
If `π` is a packing permutation for `h` with parameters `(H,S)`, then meeting the
targets for `h` on the permuted schedule is equivalent to `Nstar k H S ≤ n`. -/
theorem exact_finish_time_general_of_packing
    {k : Nat} (hk : 0 < k) {h : Fin k → Nat} {π : Equiv (Fin k) (Fin k)} {H S : Nat}
    (ip : IsPacking k h π H S) :
    ∀ n, targetsMet (permuteSchedule π (roundRobin k hk)) h n ↔ Nstar k H S ≤ n := by
  intro n
  -- Move targets across the axis relabeling…
  have perm := targetsMet_permute (π := π) (τ := roundRobin k hk) (h := h) (n := n)
  -- …then apply the packed API to `h ∘ π⁻¹`
  have pp : PackedProfile k (fun i => h (π.symm i)) H S := ip.toPackedProfile
  have packed := targetsMet_iff_ge_Nstar_packed (k := k) hk
                    (h := fun i => h (π.symm i)) (H := H) (S := S) pp n
  exact perm.trans packed

/-- Immediate corollary: at `N*` itself, `h` is met on the permuted schedule. -/
theorem targetsMet_at_Nstar_general_of_packing
    {k : Nat} (hk : 0 < k) {h : Fin k → Nat} {π : Equiv (Fin k) (Fin k)} {H S : Nat}
    (ip : IsPacking k h π H S) :
    targetsMet (permuteSchedule π (roundRobin k hk)) h (Nstar k H S) := by
  have := exact_finish_time_general_of_packing (k := k) hk (h := h) (π := π) (H := H) (S := S) ip
  simpa using (this (Nstar k H S)).mpr (Nat.le_refl _)

/-- **General lower bound (targetsMet view).**
If `π` packs `h` with parameters `(H,S)` and `H>0`,
then `h` cannot be met below `N*` on the permuted schedule. -/
theorem not_targetsMet_below_Nstar_general_of_packing
    {k : Nat} (hk : 0 < k) {h : Fin k → Nat} {π : Equiv (Fin k) (Fin k)} {H S : Nat}
    (ip : IsPacking k h π H S) (hH : 0 < H) :
    ∀ {n}, n < Nstar k H S →
      ¬ targetsMet (permuteSchedule π (roundRobin k hk)) h n := by
  intro n hn
  -- Move to permuted targets: h ∘ π⁻¹ on the original schedule
  have perm :=
    (targetsMet_permute (π := π) (τ := roundRobin k hk) (h := h) (n := n)).trans
      (Iff.intro (fun hmet => hmet) (fun hmet => hmet))  -- syntactic noise suppressor
  -- Apply the packed negation lemma with the packed profile induced by `ip`
  have pp : PackedProfile k (fun i => h (π.symm i)) H S := ip.toPackedProfile
  have packed_fail :=
    not_targetsMet_below_Nstar_packed_of (k := k) hk (h := fun i => h (π.symm i))
      (H := H) (S := S) (pp := pp) hH (n := n) (by
        -- `hn : n < Nstar …` is already in the form expected by the packed lemma
        exact hn)
  -- rewrite the goal with `targetsMet_permute`
  -- `perm` is precisely `targetsMet (permute …) h n ↔ targetsMet (roundRobin …) (h ∘ π⁻¹) n`
  simpa [perm] using packed_fail

/-! ### Permutation convenience lemmas -/

/-- Identity permutation leaves the schedule unchanged. -/
@[simp] lemma permuteSchedule_id {k} (τ : Schedule k) :
    permuteSchedule (Equiv.refl (Fin k)) τ = τ := rfl

/-- Permuting by `π` and then by `ρ` equals permuting by their composition. -/
@[simp] lemma permuteSchedule_comp {k}
    (π ρ : Equiv (Fin k) (Fin k)) (τ : Schedule k) :
    permuteSchedule (π.trans ρ) τ =
      permuteSchedule π (permuteSchedule ρ τ) := rfl

/-! ### General case theorem scaffolding 

Note: The constructive packing permutation that satisfies `IsPacking`
is left as future work. Once constructed, it plugs directly into the
theorems above to give the complete general case.
-/

/-! ### Example usage pattern

This shows how to use the permutation machinery to reduce general
profiles to the packed case. The actual packing permutation construction
is left for future implementation.
-/

section UsageExample
  variable {k : Nat} (hk : 0 < k) (h : Fin k → Nat) (H S : Nat)
  variable (π : Equiv (Fin k) (Fin k))
  
  -- Suppose π packs the H-level axes first so that h ∘ π⁻¹ is packed
  variable (packed' : PackedProfile k (fun i => h (π.symm i)) H S)
  
  -- Then the packed exactness theorem applies to the permuted targets
  theorem exact_permuted_targets (packed' : PackedProfile k (fun i => h (π.symm i)) H S) :
      ∀ n, targetsMet (roundRobin k hk) (fun i => h (π.symm i)) n ↔ Nstar k H S ≤ n :=
    targetsMet_iff_ge_Nstar_packed (k := k) hk (h := fun i => h (π.symm i)) (H := H) (S := S) packed'
  
  -- And we can translate back to the original targets on the permuted schedule
  theorem exact_original_targets_on_permuted 
      (packed' : PackedProfile k (fun i => h (π.symm i)) H S) :
      ∀ n, targetsMet (permuteSchedule π (roundRobin k hk)) h n ↔ Nstar k H S ≤ n := by
    intro n
    rw [targetsMet_permute]
    exact exact_permuted_targets hk h H S π packed' n
end UsageExample

section Sanity
  example : Nstar 3 0 7 = 0 := by simp
  example : Nstar 4 (Nat.succ 2) 1 = 4*2 + 1 := by simp
end Sanity

end Papers.P4Meta