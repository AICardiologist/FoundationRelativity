# Consultation Memo: Infrastructure Lemma Refactoring Strategy

**To:** Senior Professor
**From:** Agent
**Date:** September 30, 2025
**Re:** Tactical guidance on refactoring infrastructure lemmas in Priority 2

---

## Executive Summary

Welcome back! We're 75% through your TRUE LEVEL 3 plan but hit a tactical blocker with infrastructure lemma proofs. **Need your guidance on 3 strategic decisions** to complete the final push.

**Current Achievement:**
- ✅ Zero axioms (AX_differentiable_hack eliminated)
- ✅ 4 out of 5 original sorries eliminated
- ⚠️ 4 temporary infrastructure sorries added (sound, just need tactics)
- 📊 Build: 27 errors remaining (down from ~40)

---

## Complete Background Recap

### Project Context: Paper 5 (General Relativity) Axiom Calibration

**File:** `Papers/P5_GeneralRelativity/GR/Riemann.lean`

**Research Standard:** Publication requires TRUE LEVEL 3 formalization:
- **Zero project-specific axioms**
- **Zero sorries** (no admitted facts)

**Why This Matters:** We're formalizing the Riemann curvature tensor and proving the Bianchi identity (alternation property) for Schwarzschild spacetime. This is foundational for proving Einstein's field equations are satisfied.

### The Original Problem (Pre-Vacation)

**Starting State (before your vacation):**
- ❌ 1 project axiom: `AX_differentiable_hack`
- ❌ 5 active sorries in Riemann.lean
- ✅ Build passing (3078 jobs)
- Status: "Level 2.999" - almost rigorous but not publication-ready

**The Axiom:**
```lean
axiom AX_differentiable_hack :
  ∀ (f : ℝ → ℝ → ℝ) (r θ : ℝ),
    DifferentiableAt ℝ (fun x => f x θ) r ∧
    DifferentiableAt ℝ (fun y => f r y) θ
```

**Why Unsound:** Claimed ALL functions ℝ → ℝ → ℝ are differentiable everywhere (false - e.g., step functions aren't differentiable).

**The 5 Sorries:**
1. Line 713: `dCoord_add` - used AX_differentiable_hack for arbitrary functions
2. Line 719: `dCoord_sub` - used AX_differentiable_hack for arbitrary functions
3. Line 725: `dCoord_mul` - used AX_differentiable_hack for arbitrary functions
4. Line 1953: `mu_t_component_eq` - Stage-2 preview (unused scaffolding)
5. Line 2010: `Riemann_alternation` - main alternation proof (commented out due to "performance issues")

### Your Pre-Vacation Guidance (Complete Plan)

You provided a definitive 3-priority plan in your last consultation:

**🎯 Priority 1: Delete Stage2_mu_t_preview namespace** (lines 1926-1955)
- Rationale: Unused preview code, just scaffolding
- Expected: 1 sorry eliminated
- Time: 5-10 minutes

**🎯 Priority 2: Delete dCoord_add/sub/mul and refactor ALL call sites**
- Rationale: These lemmas are fundamentally unsound (arbitrary function differentiability)
- Expected: 3 sorries eliminated
- Strategy: Replace with axiom-free `_of_diff` versions that require explicit differentiability proofs
- Time: 2-4 hours

**🎯 Priority 3: Optimize and activate Riemann_alternation proof**
- Rationale: Proof exists but is commented out due to "performance issues"
- Strategy: Apply your "Controlled Rewriting Sequence" optimization:
  1. `abel_nf` - canonicalize additive structure
  2. `simp only [regrouping lemmas]` - structural transforms
  3. `ring_nf` - final arithmetic normalization
- Expected: 1 sorry eliminated
- Time: 4-8 hours

**Total Path to TRUE LEVEL 3:** 6-12 hours estimated

---

## What We Accomplished (Phase 1: Axiom Elimination)

**Before your vacation, we completed:**

1. ✅ **Proved Christoffel symbols are differentiable** (1 hour)
   - Added actual proofs for `Γ_differentiable_r` and `Γ_differentiable_θ`
   - These are the concrete functions we care about (not arbitrary functions)

2. ✅ **Created axiom-free versions** with `@[simp]` attribute
   - `dCoord_add_of_diff` - requires differentiability proofs
   - `dCoord_sub_of_diff` - requires differentiability proofs
   - `dCoord_mul_of_diff` - requires differentiability proofs
   - These have `@[simp]` so simp tactic uses them automatically

3. ✅ **Deleted AX_differentiable_hack axiom** (15 minutes)
   - Build passed! All simp calls automatically switched to `@[simp]` versions

4. ✅ **Schwarzschild.lean: Zero axioms, zero sorries** (2+ hours of fixes)
   - Critical path for publication is now completely rigorous

**Result:** Zero project axioms achieved! ✅

---

## What We Accomplished (Phase 2: Priority 1 & 2 Execution)

### Priority 1: COMPLETE ✅

**Deleted:** `Stage2_mu_t_preview` namespace (lines 1926-1955)
- Removed unused preview lemma `mu_t_component_eq`
- **1 sorry eliminated**
- Build passed immediately after deletion
- Time: 5 minutes

### Priority 2: 75% COMPLETE ⚠️

**Deleted:** 3 unsound legacy lemmas (lines 713, 719, 725)
```lean
-- DELETED (these were fundamentally unsound):
lemma dCoord_add (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ) :
  dCoord μ (fun r θ => f r θ + g r θ) r θ =
  dCoord μ f r θ + dCoord μ g r θ := by
  apply dCoord_add_of_diff
  all_goals { left; sorry }  -- ❌ Can't prove arbitrary f, g differentiable
```
- **3 sorries eliminated**

**Refactored (completed):**

1. ✅ Fixed syntax error (line 705) - doc comment format
2. ✅ Fixed simp calls (lines 936, 1476) - removed deleted lemma references
3. ✅ Converted 4 `dCoord_mul` uses to `dCoord_mul_of_diff` (lines 1594, 1637, 1689, 1733)
   - Added differentiability proofs using `discharge_diff` tactic
   - Pattern: `(by discharge_diff) (by discharge_diff) (by discharge_diff) (by discharge_diff)`

**Example of successful refactoring:**
```lean
-- Before (used deleted lemma):
simpa using dCoord_mul c
  (fun r θ => Γtot M r θ Idx.t d a)
  (fun r θ => g M Idx.t b r θ) r θ

-- After (axiom-free with proofs):
simpa using dCoord_mul_of_diff c
  (fun r θ => Γtot M r θ Idx.t d a)
  (fun r θ => g M Idx.t b r θ) r θ
  (by discharge_diff) (by discharge_diff)
  (by discharge_diff) (by discharge_diff)
```

**Time invested so far:** ~2.5 hours

---

## Current Blocker: Infrastructure Lemma Tactics

### The Problem

**Infrastructure helper lemmas** built on top of deleted lemmas now need refactoring:

1. `dCoord_add4` - distributes dCoord over 4-term sums (A + B + C + D)
2. `dCoord_add4_flat` - flattened version used by call sites
3. `dCoord_sumIdx` - distributes dCoord over index sums (Σᵢ Fᵢ)
4. `dCoord_sumIdx_via_funext` - bridge lemma for call sites

**These lemmas are used ~25 times** in the Stage1 LHS proofs and other places.

### The Tactical Challenge

**Goal:** Refactor `dCoord_add4` to use `dCoord_add_of_diff` instead of deleted `dCoord_add`.

**New signature (correct - requires proofs):**
```lean
lemma dCoord_add4 (μ : Idx) (A B C D : ℝ → ℝ → ℝ) (r θ : ℝ)
    (hA_r : DifferentiableAt_r A r θ ∨ μ ≠ Idx.r)
    (hB_r : DifferentiableAt_r B r θ ∨ μ ≠ Idx.r)
    (hC_r : DifferentiableAt_r C r θ ∨ μ ≠ Idx.r)
    (hD_r : DifferentiableAt_r D r θ ∨ μ ≠ Idx.r)
    (hA_θ : DifferentiableAt_θ A r θ ∨ μ ≠ Idx.θ)
    (hB_θ : DifferentiableAt_θ B r θ ∨ μ ≠ Idx.θ)
    (hC_θ : DifferentiableAt_θ C r θ ∨ μ ≠ Idx.θ)
    (hD_θ : DifferentiableAt_θ D r θ ∨ μ ≠ Idx.θ) :
  dCoord μ (fun r θ => A r θ + B r θ + C r θ + D r θ) r θ =
  dCoord μ A r θ + dCoord μ B r θ + dCoord μ C r θ + dCoord μ D r θ
```

**Proof strategy (should work in principle):**

Apply `dCoord_add_of_diff` three times to split (A+B+C+D) → ((A+B+C)+D) → ((A+B)+C)+D → (A+B)+C+D

**But need intermediate proofs like:**
```lean
hab_r : DifferentiableAt_r (fun r θ => A r θ + B r θ + C r θ) r θ ∨ μ ≠ Idx.r
```

**From hypotheses:**
```lean
hA_r : DifferentiableAt_r A r θ ∨ μ ≠ Idx.r
hB_r : DifferentiableAt_r B r θ ∨ μ ≠ Idx.r
hC_r : DifferentiableAt_r C r θ ∨ μ ≠ Idx.r
```

### Attempted Tactics (All Failed)

**Attempt 1: Cases exhaustion**
```lean
have hab_r : DifferentiableAt_r (fun r θ => A r θ + B r θ + C r θ) r θ ∨ μ ≠ Idx.r := by
  cases hA_r <;> cases hB_r <;> cases hC_r <;> simp_all [DifferentiableAt_r]
  -- ❌ TIMEOUT at 200000 heartbeats
```
Problem: 8 cases × 8 cases × 8 cases = 512 branches, simp_all explodes

**Attempt 2: Calc chain**
```lean
calc dCoord μ (fun r θ => A r θ + B r θ + C r θ + D r θ) r θ
    = dCoord μ (fun r θ => (A r θ + B r θ + C r θ) + D r θ) r θ := by rfl
  _ = dCoord μ (fun r θ => A r θ + B r θ + C r θ) r θ + dCoord μ D r θ :=
      dCoord_add_of_diff (by assumption) hD_r (by assumption) hD_θ
      -- ❌ Type mismatch - expects composite function proof
```
Problem: Can't just use `assumption` for composite function differentiability

**Attempt 3: Manual construction**
Too verbose, got lost in type errors

### Current Workaround

**Added `sorry` placeholders with clear documentation:**
```lean
lemma dCoord_add4 (μ : Idx) (A B C D : ℝ → ℝ → ℝ) (r θ : ℝ)
    (hA_r : DifferentiableAt_r A r θ ∨ μ ≠ Idx.r)
    ... := by
  sorry  -- TODO: Prove using repeated application of dCoord_add_of_diff
  -- This is sound - just needs tactics that don't timeout
```

**Why this is acceptable (temporarily):**
- These lemmas **are mathematically sound**
- The theorems they state are true
- They **should be provable** from `dCoord_add_of_diff`
- We just need the right tactic pattern

**Impact:**
- Added 4 temporary sorries to infrastructure
- But still eliminated 4 original sorries (net: same sorry count as when you left)
- Build has 27 errors (call sites need hypothesis discharge)

---

## Key Technical Definitions (For Reference)

```lean
-- Directional differentiability predicates (defined in our codebase)
def DifferentiableAt_r (f : ℝ → ℝ → ℝ) (r θ : ℝ) : Prop :=
  DifferentiableAt ℝ (fun x => f x θ) r

def DifferentiableAt_θ (f : ℝ → ℝ → ℝ) (r θ : ℝ) : Prop :=
  DifferentiableAt ℝ (fun y => f r y) θ

-- The axiom-free lemma (already proven, has @[simp])
@[simp] lemma dCoord_add_of_diff (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ)
    (hf_r : DifferentiableAt_r f r θ ∨ μ ≠ Idx.r)
    (hg_r : DifferentiableAt_r g r θ ∨ μ ≠ Idx.r)
    (hf_θ : DifferentiableAt_θ f r θ ∨ μ ≠ Idx.θ)
    (hg_θ : DifferentiableAt_θ g r θ ∨ μ ≠ Idx.θ) :
    dCoord μ (fun r θ => f r θ + g r θ) r θ =
    dCoord μ f r θ + dCoord μ g r θ := by
  cases μ <;> simp [dCoord, DifferentiableAt_r, DifferentiableAt_θ] <;>
  (first | apply deriv_add | rfl) <;> assumption

-- Custom tactic for concrete functions (works well)
syntax "discharge_diff" : tactic
macro_rules
| `(tactic| discharge_diff) =>
  `(tactic| first
    | apply Γ_differentiable_r  -- Christoffel symbols
    | apply Γ_differentiable_θ
    | apply g_differentiable_r   -- Metric components
    | apply g_differentiable_θ
    | exact Or.inr rfl           -- When μ ≠ direction
    | assumption)
```

---

## Strategic Questions for Professor

### Q1: Infrastructure Lemma Strategy

**Given 4 infrastructure lemmas with sound but unproven statements, which approach:**

**Option A: Keep infrastructure sorries temporarily**
- Pro: Allows fixing call site errors to see full scope
- Pro: Infrastructure is sound (just missing tactics)
- Pro: Preserves useful abstractions
- Con: Adds 4 sorries (net: same count as before vacation)
- Con: Not TRUE LEVEL 3 until resolved

**Option B: Delete infrastructure lemmas entirely**
- Pro: Forces direct use of `_of_diff` everywhere (no shortcuts)
- Pro: Eliminates infrastructure sorries immediately
- Con: ~25 call sites need individual refactoring
- Con: Loses abstraction (4-term sums become manual 3× applications)
- Con: More verbose, harder to maintain

**Option C: Invest in proving infrastructure lemmas**
- Pro: Complete, rigorous infrastructure layer
- Pro: Preserves abstractions with full rigor
- Con: Requires solving the tactic challenge (time investment)
- Con: May hit more subtle issues
- Estimated time: 2-4 hours if you provide tactic pattern

**Your recommendation?**

### Q2: Tactic Pattern for Composite Differentiability

**The core tactical problem:**

```lean
-- GIVEN hypotheses about individual functions:
hA_r : DifferentiableAt_r A r θ ∨ μ ≠ Idx.r
hB_r : DifferentiableAt_r B r θ ∨ μ ≠ Idx.r
hC_r : DifferentiableAt_r C r θ ∨ μ ≠ Idx.r

-- NEED to prove composite differentiability:
goal : DifferentiableAt_r (fun r θ => A r θ + B r θ + C r θ) r θ ∨ μ ≠ Idx.r

-- What tactic pattern works without 200000 heartbeat timeout?
```

**Constraints:**
- `DifferentiableAt_r` unfolds to Mathlib's `DifferentiableAt ℝ`
- Mathlib has `DifferentiableAt.add : DifferentiableAt f → DifferentiableAt g → DifferentiableAt (f + g)`
- The `∨ μ ≠ Idx.r` disjunction adds case complexity (8 combinations for 3 functions)

**Your tactical guidance?** (Pattern, specific lemmas, tactic sequence?)

### Q3: Priority and Timeline

**Current state:**
- ✅ Priority 1 complete (5 min)
- ⚠️ Priority 2: 75% complete (2.5 hours invested, ~1.5-3 hours remaining depending on strategy)
- ⏳ Priority 3 pending (4-8 hours estimated)

**Timeline to TRUE LEVEL 3:**
- Optimistic: 3-6 hours (if you provide tactic pattern + Priority 3 goes smoothly)
- Realistic: 6-10 hours (with some debugging/iteration)
- Pessimistic: 10-15 hours (if fundamental issues arise)

**Questions:**
1. Should we continue systematic refactoring of Priority 2?
2. Or acceptable to checkpoint with infrastructure sorries and move to Priority 3?
3. What's the publication timeline pressure?

---

## Summary of Remaining Work

### To Complete Priority 2 (depending on your guidance):

**If Option A (keep infrastructure sorries):**
1. Fix ~20 dCoord_add4_flat call sites with hypothesis discharge
2. Fix ~5 other type mismatches
3. Get build passing (0 errors)
4. Checkpoint: 1 original sorry + 4 infrastructure sorries = 5 total
5. Move to Priority 3

**If Option B (delete infrastructure):**
1. Delete 4 helper lemmas (eliminate 4 sorries)
2. Refactor ~25 call sites to use `dCoord_add_of_diff` directly
3. Fix all type mismatches
4. Get build passing (0 errors)
5. Checkpoint: 1 original sorry (Riemann_alternation)
6. Move to Priority 3

**If Option C (prove infrastructure):**
1. Apply your tactic pattern to prove 4 infrastructure lemmas
2. Fix ~20 call sites with hypothesis discharge
3. Get build passing (0 errors)
4. Checkpoint: 1 original sorry (Riemann_alternation)
5. Move to Priority 3

### Priority 3 (after Priority 2 complete):

Uncomment and optimize Riemann_alternation proof (lines 2010-2614):
- Add `set_option maxHeartbeats 2000000`
- Apply "Controlled Rewriting Sequence": `abel_nf` → `simp only [...]` → `ring_nf`
- Debug performance issues
- **Final sorry eliminated → TRUE LEVEL 3 ACHIEVED** ✅

---

## Recommendation

**My assessment:** Option C (prove infrastructure) is best if you can provide the tactic pattern, otherwise Option B (delete infrastructure) is cleaner than Option A.

**Rationale:**
- Infrastructure lemmas are good abstractions (avoid code duplication)
- But not worth keeping as sorries long-term
- If provable quickly with your guidance → keep and prove (Option C)
- If too complex → delete and inline (Option B)

**Next steps pending your guidance:**
1. Tactic pattern for composite differentiability? → Proceed with Option C
2. No quick pattern available? → Proceed with Option B
3. Accept infrastructure sorries? → Proceed with Option A and move to Priority 3

---

**Thank you for your guidance, Professor!** Looking forward to completing TRUE LEVEL 3.
