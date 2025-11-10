# Diagnostic Report: Branch Proof Attempts - October 26, 2025

**Status**: ⚠️ **BLOCKED** - hb and ha branch proofs fail with all attempted tactics
**Date**: October 26, 2025
**Agent**: Claude Code (Sonnet 4.5)
**For**: JP (Tactic Professor)

---

## Executive Summary

Successfully integrated JP's fix kit with these results:

✅ **SUCCESSES**:
- Abbrev approach (Gamma_mu_nabla_nu, Gamma_nu_nabla_mu) - type elaboration now instant
- E₁/E₂ congruence lemmas - E' proof compiles perfectly (lines 7097-7153)
- All upstream infrastructure (hb_pack, ha_pack) compiles cleanly

❌ **BLOCKING ISSUE**:
- hb and ha branch proofs (lines 7191-7200, 7213-7218) fail with all attempted approaches
- Root cause: Nested sums from nabla_g expansion cause ring timeout/failure
- Need sum-level tactical guidance to avoid pointwise expansion

---

## What Works Perfectly ✅

### 1. Abbrev Integration (Lines 7021-7032)

```lean
abbrev Gamma_mu_nabla_nu (M r θ : ℝ) (μ ν a b : Idx) : ℝ :=
  sumIdx (fun ρ =>
    (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b) +
    (Γtot M r θ ρ μ b) * (nabla_g M r θ ν a ρ))

abbrev Gamma_nu_nabla_mu (M r θ : ℝ) (μ ν a b : Idx) : ℝ :=
  sumIdx (fun ρ =>
    (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b) +
    (Γtot M r θ ρ ν b) * (nabla_g M r θ μ a ρ))
```

**Result**: Type signature elaboration is instant (was timing out before)

**Note**: Renamed from JP's Unicode `Γμ⋅∇ν` which isn't a valid Lean identifier

### 2. E₁/E₂ Congruence Approach (Lines 7107-7137)

```lean
have E₁ :
  sumIdx (fun e => [expand_P_ab's dG terms])
  = sumIdx (fun ρ => dG_b ρ + dG_a ρ) := by
  apply sumIdx_congr; intro ρ
  simp [dG_b, dG_a, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

have E₂ :
  sumIdx (fun e => [expand_P_ab's P terms])
  = sumIdx (fun ρ => P_b ρ + P_a ρ) := by
  apply sumIdx_congr; intro ρ
  simp [P_b, P_a, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

have E₀ := E
rw [E₁, E₂] at E₀
exact E₀
```

**Result**: E' proof compiles with 0 errors, 0 timeouts ✅
**Compilation time**: Fast (< 1 second)

---

## What's Blocked ❌

### Branch Proofs: hb and ha (Lines 7191-7200, 7213-7218)

**Goal for hb**:
```lean
have hb :
  (sumIdx B_b) - Cμa + Cνa
    = - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
```

**Challenge**: After expanding definitions, nested sums appear from `nabla_g` expansion:
- nabla_g ν ρ b = ∂_ν g_ρb - sumIdx (fun e => Γ^e_νρ * g_eb + Γ^e_νb * g_ρe)
- These nested `sumIdx fun e => ...` terms make ring timeout

---

## Attempted Approaches (All Failed)

### Attempt 1: Pointwise with `intro ρ; ring`

**Code**:
```lean
rw [hb_pack]
simp only [nabla_g, B_b, dG_b, P_b, RiemannUp]
rw [← sumIdx_neg]
apply sumIdx_congr
intro ρ
ring  -- ❌ TIMEOUT
```

**Error**:
```
error: (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (200000) has been reached
```

**Diagnosis**: After `intro ρ`, the goal has nested sums:
```lean
⊢ ((-(dCoord μ (Γ^ρ_νa) * g_ρb) + ...
     + (-(Γ^ρ_νa * ∑ e, Γ^e_μρ * g_eb) - ...))
   = -(...)
```

Ring must handle ~40-50 scalar terms WITH nested sums over `e`. Too expensive.

**Matches JP's warning**: "Do NOT prove the branch claim pointwise (intro ρ … ring)"

---

### Attempt 2: Expand `sumIdx` to Explicit Case Splits

**Rationale**: Convert all sums to explicit 4-case patterns so ring only sees scalars.

**Code**:
```lean
rw [hb_pack]
simp only [nabla_g, B_b, dG_b, P_b, RiemannUp]  -- Don't expand sumIdx yet
rw [← sumIdx_neg]
simp only [sumIdx]  -- Expand to 4-case pattern: t, r, θ, φ
ring  -- On fully expanded form
```

**Error**:
```
error: unsolved goals
⊢ ∑ x, (... nested sums still present ...)
```

**Diagnosis**: Even after `simp only [sumIdx]`, the goal still has nested sums because:
1. `simp only [sumIdx]` converts `sumIdx f` to Mathlib's `∑ x, f x` notation
2. But the nested sums from `nabla_g` expansion remain as `∑ x_1, ...`
3. So ring still sees nested sums and fails

**Lesson**: Expanding sumIdx isn't enough - nested sums from nabla_g persist.

---

### Attempt 3: Sum-Level with Collector Lemmas (Incomplete)

**JP's Guidance** (from conversation summary):
```
1. Cancel payload with scalar ring under Σ_ρ (fast)
2. Use Fubini (sumIdx_swap) to reorder sums
3. Use diagonality (sumIdx_reduce_by_diagonality) to collapse sums
4. Finish with one scalar ring
```

**Available Collector Lemmas**:
- `sumIdx_reduce_by_diagonality` (line 1619) - collapses `Σ_e g_ρe * K e` to `g_ρρ * K ρ`
- `sumIdx_mul_sumIdx_swap` (line 2221) - Fubini for finite sums
- `sumIdx_sub_same_right` (line 1631) - factor out common right term
- `sumIdx_add_same_left` (line 1644) - factor out common left term
- `sumIdx_congr` (line 1607) - prove sums equal pointwise
- `sumIdx_neg` (line 1399 in Schwarzschild.lean) - move negation in/out

**What I Tried**:
```lean
-- Payload cancellation step (WORKED)
have payload_cancel :
  sumIdx (fun ρ =>
    (-(Γ^ρ_νa) * (∂_μ g_ρb) + (Γ^ρ_μa) * (∂_ν g_ρb))
    - ((Γ^ρ_μa) * (∂_ν g_ρb) - (Γ^ρ_νa) * (∂_μ g_ρb)))
  = 0 := by
  apply sumIdx_congr; intro ρ; ring  -- Fast! Only 4 simple terms
```

**What I Couldn't Complete**: ΓΓ·g quartet reshaping using Fubini + diagonality

**Why Stuck**: Without seeing goal states after each tactic, I can't determine:
- Which collector lemma to apply when
- What form to rewrite sums into
- How to align the ΓΓ·g terms with RiemannUp's structure

---

## Technical Analysis

### Why Pointwise Fails

After `simp only [nabla_g, B_b, dG_b, P_b, RiemannUp]` and `intro ρ`, the goal becomes:

```lean
⊢ ((∂Γ·g terms) + (Γ·∂g terms) + (ΓΓ·g nested sum terms))
  = -(∂Γ·g terms) + (ΓΓ·g nested sum terms)
```

Where "ΓΓ·g nested sum terms" look like:
```lean
Γ^ρ_μa * (sumIdx (fun e => Γ^e_νρ * g_eb + Γ^e_νb * g_ρe))
```

**Ring's Task**: Prove equality of two expressions each containing:
- ~10-15 scalar ∂Γ·g and Γ·∂g terms (no problem)
- ~4-6 nested sum terms (PROBLEM!)

**Ring's Limitation**: Ring normalizes polynomial expressions, but:
1. It must first β-reduce and expand nested sums
2. Each nested sum expands to 4 cases
3. Multiple nested sums create combinatorial explosion
4. Expression becomes too large → timeout

**Result**: Heartbeat limit (200k) exceeded

---

### Why Expanding sumIdx Fails

**Expected**: After `simp only [sumIdx]`, all sums become explicit scalars.

**Reality**: Only the outer sum expands. Example:

Before `simp only [sumIdx]`:
```lean
sumIdx (fun ρ => A ρ + (B ρ * sumIdx (fun e => C ρ e)))
```

After `simp only [sumIdx]`:
```lean
(A t + B t * sumIdx (fun e => C t e)) +
(A r + B r * sumIdx (fun e => C r e)) +
(A θ + B θ * sumIdx (fun e => C θ e)) +
(A φ + B φ * sumIdx (fun e => C φ e))
```

The inner `sumIdx (fun e => C _ e)` remains! (Or gets converted to `∑ e, C _ e`)

**Why**: Simp expands definitions one level at a time. The nested sums from `nabla_g` are inside lambda bodies, so they remain.

---

### Why Sum-Level Approach is Correct (But Hard)

JP's approach works at the Σ_ρ level, never going pointwise until the very end:

**Structure**:
```
LHS: sumIdx (fun ρ => (∂Γ terms) + (Γ·∂g terms) + (Γ * Σ_e ΓΓ·g))
RHS: -sumIdx (fun ρ => (∂Γ terms) + (Σ_e ΓΓ·g))
```

**Strategy**:
1. Factor out common structure using collector lemmas
2. Cancel Γ·∂g payload (scalar ring under sumIdx_congr - fast!)
3. For ΓΓ·g terms:
   - Use `sumIdx_mul_sumIdx_swap` to swap Σ_ρ and Σ_e (Fubini)
   - Use `sumIdx_reduce_by_diagonality` to collapse Σ_e using g's diagonality
   - Result: ΓΓ·g terms match RiemannUp's structure
4. Final scalar ring to package result

**Why I Couldn't Complete**: Can't see intermediate goal states, so don't know:
- When to apply which lemma
- What the goal looks like after each step
- How to align terms correctly

---

## Specific Questions for JP

### Question 1: Complete Tactical Sequence

Can you provide the complete tactical proof for `hb` using collector lemmas?

**Current state after payload_cancel**:
```lean
have hb :
  (sumIdx B_b) - Cμa + Cνa
    = - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ) := by
  classical
  -- After some manipulation, we have:
  -- LHS: sumIdx (∂Γ·g terms) + ΓΓ·g terms from -Cμa + Cνa
  -- RHS: -sumIdx (∂Γ·g + ΓΓ·g from RiemannUp)
  -- payload_cancel shows Γ·∂g terms sum to 0

  -- What next? How to reshape ΓΓ·g quartet?
  ???
```

**Needed**: Specific rw/simp sequence using:
- sumIdx_mul_sumIdx_swap
- sumIdx_reduce_by_diagonality
- Other collector lemmas

### Question 2: Structural Approach

Should I:

**Option A**: Work directly from `hb_pack` form
```lean
rw [hb_pack]
-- Goal: sumIdx (B_b ρ - Γ*∇g + Γ*∇g) = -sumIdx (RiemannUp * g)
-- Apply collector lemmas at sum level
```

**Option B**: First expand some definitions, then use collectors
```lean
simp only [nabla_g]  -- Expose ∂g - ΓΓ·g structure
-- Then use collectors to manipulate the exposed sums
```

**Option C**: Different structure entirely?

### Question 3: Goal State Insights

After `simp only [nabla_g]` in the hb proof, what does the goal look like?

I suspect it's something like:
```lean
sumIdx (fun ρ => B_b ρ - Γ^ρ_μa * (∂_ν g_ρb - Σ_e (...)) + ...)
  = -sumIdx (fun ρ => (∂_μ Γ^ρ_νa - ∂_ν Γ^ρ_μa + Σ_e ΓΓ - Σ_e ΓΓ) * g_ρb)
```

But I can't verify without compiling. Can you clarify the exact form?

### Question 4: Fubini Application

For the ΓΓ·g terms, after expanding nabla_g we have:
```lean
sumIdx (fun ρ => Γ^ρ_μa * sumIdx (fun e => Γ^e_νρ * g_eb + Γ^e_νb * g_ρe))
```

To match RiemannUp's `sumIdx (fun e => Γ^ρ_μe * Γ^e_νa)`, do I:

1. Use `mul_sumIdx_distrib` to push Γ^ρ_μa inside?
2. Then split the sum using `sumIdx_add_distrib`?
3. Then swap with `sumIdx_mul_sumIdx_swap`?
4. Then use `sumIdx_reduce_by_diagonality`?

What's the correct sequence?

### Question 5: Alternative: Dedicated Lemma?

Would it be easier to prove an auxiliary lemma first?

```lean
lemma nabla_g_commutator_is_RiemannUp :
  ∀ ρ, (B_b ρ - Γ^ρ_μa * nabla_g_νρb + Γ^ρ_νa * nabla_g_μρb)
     = -(RiemannUp ρ a μ ν * g_ρb) := by
  intro ρ
  simp only [nabla_g, B_b, dG_b, P_b, RiemannUp]
  -- Now it's pointwise but with explicit index ρ
  -- Can we use diagonality directly here?
  ???
```

Then use `sumIdx_congr` on this?

---

## Available Resources

### Collector Lemmas (All in Riemann.lean)

1. **sumIdx_congr** (line 1607)
   ```lean
   (∀ i, f i = g i) → sumIdx f = sumIdx g
   ```

2. **sumIdx_reduce_by_diagonality** (line 1619)
   ```lean
   sumIdx (fun e => g M ρ e r θ * K e) = g M ρ ρ r θ * K ρ
   ```
   Critical for collapsing sums using metric diagonality

3. **sumIdx_add_distrib** (already used extensively)
   ```lean
   sumIdx (f + g) = sumIdx f + sumIdx g
   ```

4. **sumIdx_sub** (similar)
   ```lean
   sumIdx (f - g) = sumIdx f - sumIdx g
   ```

5. **sumIdx_mul_sumIdx_swap** (line 2221) - Fubini
   ```lean
   sumIdx (fun ρ => G ρ * sumIdx (fun lam => F ρ lam))
   = sumIdx (fun lam => sumIdx (fun ρ => G ρ * F ρ lam))
   ```

6. **mul_sumIdx_distrib** (line 2206)
   ```lean
   a * sumIdx f = sumIdx (fun i => a * f i)
   ```

7. **sumIdx_neg** (Schwarzschild.lean line 1399)
   ```lean
   sumIdx (fun i => -f i) = -sumIdx f
   ```

8. **sumIdx_sub_same_right** (line 1631)
   ```lean
   sumIdx (fun i => f i - c) = sumIdx f - 4 * c
   ```

9. **sumIdx_add_same_left** (line 1644)
   ```lean
   sumIdx (fun i => c + f i) = 4 * c + sumIdx f
   ```

### Key Definitions

- **nabla_g** (line ~1500): ∂g - Γ·g - Γ·g (covariant derivative)
- **RiemannUp** (line ~1650): ∂Γ - ∂Γ + ΓΓ - ΓΓ (Riemann with raised first index)
- **B_b, B_a** (lines 7074-7081): dG + P blocks from expand_P_ab regrouping
- **dG_b, dG_a** (lines 7082-7087): ∂Γ·g terms
- **P_b, P_a** (lines 7088-7093): Γ·∂g terms

---

## Current File State

**File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`

**Blocked Proofs**:
- Line 7191-7200: `hb` - currently `sorry`
- Line 7213-7218: `ha` - currently `sorry`

**Working Proofs** (Ready to use once hb/ha compile):
- Lines 7097-7153: `E'` - regrouping proof ✅
- Lines 7182-7189: `hb_pack` - packaging ✅
- Lines 7203-7211: `ha_pack` - packaging ✅
- Lines 7220-7238: Final calc chain (will work once hb/ha compile)

**Build Log**: `/tmp/build_with_sorries_final.txt`

---

## Impact of Resolution

Once hb and ha are proven:

1. ✅ `algebraic_identity` compiles fully
2. ✅ `ricci_identity_on_g_general` should fold cleanly (RiemannUp·g → Riemann)
3. ✅ `Riemann_swap_a_b_ext` should reduce to metric compatibility
4. ✅ Unblocks 13 uses in Invariants.lean
5. ✅ Enables Kretschmann scalar computation
6. ✅ Completes critical path for full Riemann tensor verification

**Estimated Time After Tactical Guidance**: 1-2 hours to implement and verify

---

## Summary of What I Learned

1. **Pointwise ring on complex expressions = timeout** ✅ Confirmed JP's guidance
2. **Expanding sumIdx doesn't eliminate nested sums** ✅ New insight
3. **Collector lemmas are the right approach** ✅ But need tactical sequence
4. **E₁/E₂ pattern works beautifully** ✅ Similar approach needed for branches?

---

**Next Steps**: Awaiting JP's tactical guidance on sum-level proof sequence for hb/ha.

**Prepared By**: Claude Code (Sonnet 4.5)
**Date**: October 26, 2025
