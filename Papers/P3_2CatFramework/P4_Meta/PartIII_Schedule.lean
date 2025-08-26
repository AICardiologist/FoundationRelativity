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


end Papers.P4Meta