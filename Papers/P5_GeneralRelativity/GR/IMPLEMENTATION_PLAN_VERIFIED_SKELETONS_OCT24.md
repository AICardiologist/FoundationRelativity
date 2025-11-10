# Implementation Plan: Verified Four-Block Strategy
**Date**: October 24, 2025
**Status**: ✅ Math verified, ready to implement
**Estimated Time**: 2-3 hours

---

## Current Situation

**Good News**:
✅ Senior Professor verified corrected strategy as mathematically sound
✅ JP provided complete, bounded proof skeletons
✅ All tactical patterns documented (Q1, Q2, Q3 fixes)
✅ Build is stable (0 errors, 23 sorries)

**What Needs to Change**:
❌ Current Riemann.lean has lemmas based on FLAWED strategy
✅ Need to replace with CORRECTED strategy per JP's skeletons

---

## Required Changes to Riemann.lean

### 1. Block 0: Replace 4 Flawed Lemmas with 1 Correct Lemma

**DELETE** (Lines 6300-6371):
- `expand_P_pointwise_a` - computes P(ρ,b) ← WRONG object
- `expand_P_pointwise_b` - computes P(a,ρ) ← WRONG object
- `expand_Pa` - sums wrong pointwise ← WRONG
- `expand_Pb` - sums wrong pointwise ← WRONG

**REPLACE WITH**:
```lean
lemma expand_P_ab (M r θ : ℝ) (μ ν a b : Idx) :
  (dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ
 - dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ)
=
  -- (∂Γ)·g block (P_{∂Γ})
  (sumIdx (fun e =>
      -(dCoord μ (fun r θ => Γtot M r θ e ν a) r θ) * g M e b r θ
      + (dCoord ν (fun r θ => Γtot M r θ e μ a) r θ) * g M e b r θ
      -(dCoord μ (fun r θ => Γtot M r θ e ν b) r θ) * g M a e r θ
      + (dCoord ν (fun r θ => Γtot M r θ e μ b) r θ) * g M a e r θ))
+
  -- Γ·∂g block (P_payload)
  (sumIdx (fun e =>
      -(Γtot M r θ e ν a) * dCoord μ (fun r θ => g M e b r θ) r θ
      + (Γtot M r θ e μ a) * dCoord ν (fun r θ => g M e b r θ) r θ
      -(Γtot M r θ e ν b) * dCoord μ (fun r θ => g M a e r θ) r θ
      + (Γtot M r θ e μ b) * dCoord ν (fun r θ => g M a e r θ) r θ))
```

**Key**: This expands P(a,b) DIRECTLY (the correct object!)

---

###2. Block A: Update to "Σ of Zeros" Pattern

**Current** (Lines 6377-6420):
- Has correct *structure* (payload_cancel_a/b/all)
- But uses WRONG tactical approach (sumIdx_congr fails)

**UPDATE TO**:
```lean
lemma payload_cancel_total (M r θ : ℝ) (μ ν a b : Idx) :
  P_payload M r θ μ ν a b + Cprime_payload M r θ μ ν a b = 0 := by
  classical
  ring_nf  -- Combine to single Σ

  -- Prove pointwise body = 0
  have hpt : ∀ e : Idx,
    (-(Γ e ν a) * ∂μ g_e_b + (Γ e μ a) * ∂ν g_e_b
     -(Γ e ν b) * ∂μ g_a_e + (Γ e μ b) * ∂ν g_a_e)
  + (-(Γ e μ a) * ∂ν g_e_b + (Γ e ν a) * ∂μ g_e_b
     -(Γ e μ b) * ∂ν g_a_e + (Γ e ν b) * ∂μ g_a_e) = 0 := by
    intro e; ring

  -- Lift to Σ: KEY FIX - rewrite RHS as Σ of zeros!
  have : sumIdx (fun _ : Idx => 0 : ℝ) = 0 := by simpa using sumIdx_zero
  have hΣ : sumIdx (fun e => /*payload bodies*/)  = sumIdx (fun _ : Idx => 0) :=
    sumIdx_congr (fun e => hpt e)

  simpa [this]
```

**Q1 Fix Applied**: Rewrite `0` as `sumIdx (fun _ => 0)` before using `sumIdx_congr`

---

### 3. Block B: Update to Pairwise Sum (Not Individual)

**Current** (Lines 6473-6486):
```lean
lemma cross_block_zero ... :
  C'_cross,a + C'_cross,b = 0  -- ✓ CORRECT signature
```

**But needs PAIRWISE proof** (not individual branch):
```lean
lemma cross_pair_zero (M r θ : ℝ) (μ ν a b : Idx) :
  Cprime_cross_a M r θ μ ν a b + Cprime_cross_b M r θ μ ν a b = 0 := by
  classical
  -- Add both branches, use Fubini
  rw [sumIdx_swap]?
  ring_nf

  -- Use diagonality to collapse e ≠ ρ
  simp [g, sumIdx_expand]

  -- Show diagonal kernel sum = 0 pointwise
  have hρ : ∀ ρ,
    (Γ ρ μ a * Γ ρ ν b - Γ ρ ν a * Γ ρ μ b)
  + (Γ ρ μ b * Γ ρ ν a - Γ ρ ν b * Γ ρ μ a) = 0 := by
    intro ρ; ring

  -- Lift to Σ (using "Σ of zeros" pattern again)
  have : sumIdx (fun _ : Idx => 0 : ℝ) = 0 := by simpa using sumIdx_zero
  have hΣ : sumIdx (fun ρ => /*kernel*/ * g M ρ ρ r θ)
            = sumIdx (fun _ : Idx => 0) := by
    apply sumIdx_congr; intro ρ
    have := hρ ρ
    ring

  simpa [this]
```

**Key**: Proves COMBINED sum = 0, not individual branches

---

### 4. Block C: Verify Sign Correctness

**Current** (Lines 6426-6446):
- Already has sorries
- Need to verify RHS signs match -R_{ba} - R_{ab}

**UPDATE TO** (per JP's skeleton):
```lean
lemma main_to_commutator (M r θ : ℝ) (μ ν a b : Idx) :
  Cprime_main M r θ μ ν a b
  =
  (sumIdx (fun e => g M e b r θ * (sumIdx (fun ρ =>
      Γtot M r θ e ν ρ * Γtot M r θ ρ μ a
    - Γtot M r θ e μ ρ * Γtot M r θ ρ ν a))))
+
  (sumIdx (fun e => g M a e r θ * (sumIdx (fun ρ =>
      Γtot M r θ e ν ρ * Γtot M r θ ρ μ b
    - Γtot M r θ e μ ρ * Γtot M r θ ρ ν b)))) := by
  classical
  -- Swap sums to factor g outside
  repeat' rw [sumIdx_swap]

  -- Reorder scalars pointwise (Q3 fix)
  apply congrArg2 (·+·) <;>
    apply sumIdx_congr; intro e
    apply sumIdx_congr; intro ρ
    ring_nf
```

**Q3 Fix Applied**: Use `repeat' rw [sumIdx_swap]` then nested `sumIdx_congr` with `ring_nf`

---

### 5. Block D: Similar to Block C

**Current** (Lines 6451-6469):
- Already has sorries
- Needs sign verification

**UPDATE TO** (per JP):
```lean
lemma dGamma_match (M r θ : ℝ) (μ ν a b : Idx) :
  P_dGamma M r θ μ ν a b
  =
  (sumIdx (fun e => g M e b r θ * (-(dCoord μ (fun r θ => Γtot M r θ e ν a) r θ)
                                   +  (dCoord ν (fun r θ => Γtot M r θ e μ a) r θ))))
+
  (sumIdx (fun e => g M a e r θ * (-(dCoord μ (fun r θ => Γtot M r θ e ν b) r θ)
                                   +  (dCoord ν (fun r θ => Γtot M r θ e μ b) r θ)))) := by
  classical
  -- Factor g to outside with collectors
  ring_nf
  apply congrArg2 (·+·) <;>
    apply sumIdx_congr; intro e
    ring
```

---

### 6. clairaut_g: Keep but Implement

**Current** (Line 6283-6291):
```lean
cases ρ <;> cases b <;> simp [g, dCoord] <;> sorry
```

**IMPLEMENT** (per JP/SP):
```lean
lemma clairaut_g ... := by
  classical
  -- Case on (ρ,b)
  -- Off-diagonals: simp [g, dCoord] (trivial, g=0)
  -- Diagonals: use ContDiffAt + Mathlib Clairaut
  cases ρ <;> cases b <;> simp [g, dCoord]
  -- For diagonals (not closed yet), apply Mathlib Clairaut:
  all_goals (
    -- Use contDiffAt lemmas already proven
    -- Apply Mathlib's mixed partials theorem
    -- Details depend on exact Mathlib lemma names
    admit  -- TODO: Connect to Mathlib Clairaut
  )
```

**Note**: This requires finding the right Mathlib lemma for C² → mixed partials commute

---

## Implementation Strategy

### Phase 1: Foundation (45 min)

**Step 1.1**: Implement `clairaut_g` (15 min)
- Case analysis on indices
- Off-diagonals: trivial (g=0)
- Diagonals: Link to Mathlib (or admit temporarily)

**Step 1.2**: Replace Block 0 lemmas with `expand_P_ab` (30 min)
- Delete old 4 lemmas (lines 6300-6371)
- Add new single `expand_P_ab` lemma
- Follow JP's skeleton exactly
- Test build

### Phase 2: Blocks A, B (45 min)

**Step 2.1**: Implement `payload_cancel_total` (25 min)
- Use "Σ of zeros" pattern (Q1 fix)
- Prove pointwise cancellation with `ring`
- Lift to Σ with correct RHS rewrite
- Test build

**Step 2.2**: Implement `cross_pair_zero` (20 min)
- Pairwise sum (not individual)
- Diagonality + kernel cancellation
- Use "Σ of zeros" pattern
- Test build

### Phase 3: Blocks C, D (30 min)

**Step 3.1**: Implement `main_to_commutator` (15 min)
- Swap sums with `repeat' rw [sumIdx_swap]`
- Nested `sumIdx_congr` + `ring_nf` (Q3 fix)
- Test build

**Step 3.2**: Implement `dGamma_match` (15 min)
- Factor g with collectors
- `sumIdx_congr` + `ring`
- Test build

### Phase 4: Final Assembly (15 min)

**Step 4.1**: Wire all blocks in `algebraic_identity`
- Rewrite by block lemmas
- Use `ring_nf` to flatten
- Test final build

**Total Estimated Time**: 2 hours 15 minutes

---

## Testing Strategy

**After Each Phase**:
```bash
cd /Users/quantmann/FoundationRelativity
lake build Papers.P5_GeneralRelativity.GR.Riemann
```

**Check**:
- Error count (should be 0)
- Sorry count (should decrease by block count)
- Verify no new type errors

**Final Verification**:
- Build completes successfully
- Sorry count drops from 23 to ~16 (original)
- All Four-Block Strategy lemmas proven

---

## Potential Issues and Mitigations

### Issue 1: Clairaut Connection to Mathlib

**Problem**: May need to find exact Mathlib lemma name for C² → mixed partials

**Mitigation**:
- Search Mathlib docs for "Clairaut", "mixed partials", "fderiv_fderiv"
- Worst case: Leave as `admit` with TODO comment
- Does not block other proofs

### Issue 2: Type Unification in sumIdx_congr

**Problem**: Subtle type mismatches can cause failures

**Mitigation**:
- Follow JP's "Σ of zeros" pattern EXACTLY
- Use `have : sumIdx (fun _ => 0) = 0` first
- Then `sumIdx_congr` with explicit function match

### Issue 3: Index Naming Consistency

**Problem**: Variable names (e, ρ, lam) must match skeleton patterns

**Mitigation**:
- Copy JP's skeleton code verbatim
- Don't rename variables
- Preserve exact structure

---

## Success Criteria

✅ **Phase 1 Complete**: `clairaut_g` and `expand_P_ab` compile
✅ **Phase 2 Complete**: Blocks A and B proven, build stable
✅ **Phase 3 Complete**: Blocks C and D proven, build stable
✅ **Phase 4 Complete**: `algebraic_identity` proven, all sorries resolved

**Final State**:
```
Build: ✅ 0 errors
Sorries: ~16 (back to pre-Four-Block level)
Four-Block Strategy: ✅ Fully proven
Mathematical Correctness: ✅ Verified by Senior Professor
```

---

## Next Immediate Step

**Start with Phase 1.1**: Implement `clairaut_g`

This is:
- Independent of other blocks
- Relatively simple (case analysis)
- Required by `expand_P_ab`
- Good warm-up for the patterns

**Command**:
```bash
# Edit Riemann.lean lines 6283-6291
# Implement clairaut_g per JP's guidance
# Test build
```

---

**Status**: Ready to begin implementation
**Confidence**: High (mathematically verified strategy)
**Estimated Completion**: 2-3 hours of focused work
**Risk**: Low (bounded tactics, no recursion issues)
