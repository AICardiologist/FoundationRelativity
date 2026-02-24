# Implementation Blocker: Phase 1 Algebraic Helper Lemmas

**Date:** October 5, 2025
**Status:** BLOCKED - Need Junior Professor assistance
**Phase:** 1 (Algebraic Helper Lemmas)

---

## Context

Following Senior Professor's modular computation strategy, I'm implementing Phase 1: three simple algebraic helper lemmas for f(r) = 1 - 2M/r.

**References:**
- `MODULAR_COMPUTATION_STRATEGY.md` - Full implementation plan
- `FOLLOW_UP_TO_SENIOR_PROFESSOR.md` - Senior Professor's guidance

---

## The Blocker

I'm unable to prove two algebraic identities that should be trivial:

### Lemma 1: r_mul_f
```lean
@[simp] lemma r_mul_f (M r : ℝ) (hr_nz : r ≠ 0) : r * f M r = r - 2*M := by
  unfold f
  field_simp [hr_nz]
  ring  -- FAILS
```

**Expected:** Mathematically trivial: `r · (1 - 2M/r) = r - 2M`
**Actual error:**
```
unsolved goals
M r : ℝ
hr_nz : r ≠ 0
⊢ r * f M r = r - M * 2
```

**Note:** `field_simp` doesn't seem to unfold `f` even after `unfold f`.

### Lemma 2: one_minus_f
```lean
@[simp] lemma one_minus_f (M r : ℝ) (hr_nz : r ≠ 0) :
    1 - f M r = 2*M / r := by
  unfold f
  field_simp [hr_nz]  -- FAILS
```

**Expected:** Mathematically trivial: `1 - (1 - 2M/r) = 2M/r`
**Actual error:**
```
unsolved goals
M r : ℝ
hr_nz : r ≠ 0
⊢ 1 - f M r = M * 2 / r
```

---

## What I've Tried

1. **Attempt 1:** `simp [f]; ring` - Failed (ring can't handle division)
2. **Attempt 2:** `field_simp [f, hr_nz]; ring` - Failed (f not unfolded)
3. **Attempt 3:** `unfold f; field_simp [hr_nz]; ring` - Still fails

---

## Context: f(r) Definition

From Schwarzschild.lean:42:
```lean
noncomputable def f (M r : ℝ) : ℝ := 1 - 2*M/r
```

There's already a working derivative lemma at line 80:
```lean
theorem f_derivative (M r : ℝ) (hr : r ≠ 0) :
    deriv (fun r' => f M r') r = 2*M / r^2 := by
  simpa using (f_hasDerivAt M r hr).deriv
```

---

## Why These Lemmas Matter

**Critical dependency:** The 6 Riemann component lemmas (Phase 2) all require these algebraic identities to simplify their proofs. Without them, the modular computation strategy cannot proceed.

**From Senior Professor:**
> "To aid the automated simplifier, provide explicit lemmas for key algebraic identities involving f(r)=1−2M/r"

---

## Request for Junior Professor

### Question 1: How to prove r_mul_f?

What's the correct tactical sequence to prove `r * (1 - 2M/r) = r - 2M` for `r ≠ 0`?

**Minimal example:**
```lean
lemma r_mul_f (M r : ℝ) (hr_nz : r ≠ 0) : r * f M r = r - 2*M := by
  -- What tactics go here?
  sorry
```

### Question 2: How to prove one_minus_f?

What's the correct tactical sequence to prove `1 - (1 - 2M/r) = 2M/r` for `r ≠ 0`?

**Minimal example:**
```lean
lemma one_minus_f (M r : ℝ) (hr_nz : r ≠ 0) : 1 - f M r = 2*M / r := by
  -- What tactics go here?
  sorry
```

### Question 3: Why doesn't field_simp work after unfold?

After `unfold f`, I expected `field_simp [hr_nz]` to clear the division and allow `ring` to finish. Why doesn't this work?

---

## Files to Review

**Modified file:** `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Schwarzschild.lean`
- Lines 84-96: My attempted helper lemmas
- Line 42: Definition of `f`
- Lines 54-82: Existing f-related lemmas that work

**Implementation plan:** `MODULAR_COMPUTATION_STRATEGY.md`

**Senior Professor's guidance:** `FOLLOW_UP_TO_SENIOR_PROFESSOR.md`

---

## Impact

**Blocking:** Phase 2 (6 Riemann component lemmas)
**Blocking:** Phase 3 (Refactored Ricci_zero_ext)
**Blocking:** Complete formalization

**Once unblocked:** Can proceed with full modular computation strategy

---

**Generated:** October 5, 2025
**Priority:** HIGH - Blocking entire implementation
**Type:** Tactical Lean issue (not mathematical)
