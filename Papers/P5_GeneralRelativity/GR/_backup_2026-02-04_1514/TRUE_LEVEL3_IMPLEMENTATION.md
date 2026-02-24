# TRUE LEVEL 3 Implementation Plan - Axiom Calibration

**Date:** September 30, 2025
**Purpose:** Axiom calibration - achieve zero sorries for highest standard
**Estimated:** 2-4 hours (NOT 10-14 weeks - initial estimate was wrong!)

---

## Key Insight After Investigation

**The 10-14 week estimate was based on a misunderstanding!**

**Reality:**
- `dCoord_mul/add/sub` with `@[simp]` are used **automatically by simp tactic**
- `_of_diff` versions already exist (lines 636, 658, 680)
- We just need to **swap which ones are `@[simp]`**!

---

## Actual Implementation (2-4 hours)

### Step 1: Make _of_diff versions @[simp] ✅

**Current (lines 636-697):**
```lean
lemma dCoord_add_of_diff (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ) ...
lemma dCoord_sub_of_diff (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ) ...
lemma dCoord_mul_of_diff (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ) ...
```

**Change to:**
```lean
@[simp] lemma dCoord_add_of_diff (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ)
  (hf_r : DifferentiableAt ℝ (fun r' => f r' θ) r ∨ μ ≠ Idx.r)
  (hg_r : DifferentiableAt ℝ (fun r' => g r' θ) r ∨ μ ≠ Idx.r)
  (hf_θ : DifferentiableAt ℝ (fun θ' => f r θ') θ ∨ μ ≠ Idx.θ)
  (hg_θ : DifferentiableAt ℝ (fun θ' => g r θ') θ ∨ μ ≠ Idx.θ) :
  dCoord μ (fun r θ => f r θ + g r θ) r θ = dCoord μ f r θ + dCoord μ g r θ := by
  -- proof using differentiability hypotheses
  ...
```

### Step 2: Remove @[simp] from axiom-dependent versions

**Current (lines 702, 720, 740):**
```lean
@[simp] lemma dCoord_sub (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ) := by
  -- uses AX_differentiable_hack

@[simp] lemma dCoord_add (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ) := by
  -- uses AX_differentiable_hack

@[simp] lemma dCoord_mul (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ) := by
  -- uses AX_differentiable_hack
```

**Change to:**
```lean
-- DEPRECATED: Use dCoord_sub_of_diff instead
lemma dCoord_sub_DEPRECATED (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ) := by
  ...

-- DEPRECATED: Use dCoord_add_of_diff instead
lemma dCoord_add_DEPRECATED (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ) := by
  ...

-- DEPRECATED: Use dCoord_mul_of_diff instead
lemma dCoord_mul_DEPRECATED (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ) := by
  ...
```

### Step 3: Update discharge_diff tactic

**Current (lines 617-629):**
```lean
macro_rules
  | `(tactic| discharge_diff) => `(tactic| (
      first
      | -- Strategy 1: Prove differentiability
        simp only [DifferentiableAt_r, DifferentiableAt_θ,
                   differentiableAt_g_tt_r, ...]
      | -- Strategy 2: Prove direction mismatch
        simp [Idx.noConfusion]))
```

**This already works!** Just need to ensure it discharges all 4 hypotheses for `_of_diff` lemmas.

### Step 4: Test build

Run `lake build` - simp will now use `_of_diff` versions, which call `discharge_diff` to prove differentiability.

**Expected:** Build passes, but may discover call sites where `discharge_diff` fails.

### Step 5: Handle failures

For any failures, either:
- Add missing lemmas to `discharge_diff` database, OR
- Manually provide differentiability proofs

### Step 6: Delete AX_differentiable_hack

Once all uses eliminated, delete the sorry lemma.

---

## Why This is Fast (2-4 hours, not 10-14 weeks)

**Original misunderstanding:** Thought we needed to refactor ~200 call sites manually

**Reality:**
- simp uses `@[simp]` lemmas automatically
- Just swap which lemmas have `@[simp]` attribute
- `discharge_diff` handles most proofs automatically
- Only need to fix sites where `discharge_diff` fails

---

## Risk Assessment

**Low risk:**
- Infrastructure complete (Phase 1-2)
- `_of_diff` versions already exist
- `discharge_diff` already working
- Can test incrementally

**Potential issues:**
- Some call sites may need manual differentiability proofs
- Estimate: 10-20 sites maximum, 5-10 min each = 1-3 hours

---

## Next Steps

1. Make `_of_diff` versions `@[simp]`
2. Remove `@[simp]` from axiom-dependent versions
3. Build and test
4. Fix any `discharge_diff` failures
5. Delete `AX_differentiable_hack`
6. Verify TRUE LEVEL 3 achieved

**Let's proceed!**
