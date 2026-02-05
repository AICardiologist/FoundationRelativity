# CRITICAL: Index Convention Mismatch in nabla_g Expansion - November 17, 2024

**Status**: ❌ **BUILD FAILS** - Paul's patch cannot work as written
**For**: Paul (Tactic Professor)
**From**: Claude Code
**Date**: November 17, 2024
**Priority**: CRITICAL - Blocks all progress on Hshape implementation

---

## Executive Summary

Paul's surgical patch for `Hμ` and `Hν` **cannot work** because there is a **fundamental index convention mismatch** between:
1. The actual `nabla_g` definition (line 3213)
2. The expected expansion in Paul's patch

The `simp [nabla_g]` tactic correctly expands `nabla_g`, but produces indices in a **different order** than what the proof expects.

---

## 1. The Actual Definition (Line 3213-3216)

```lean
noncomputable def nabla_g (M r θ : ℝ) (c a b : Idx) : ℝ :=
  dCoord c (fun r θ => g M a b r θ) r θ
  - sumIdx (fun e => Γtot M r θ e c a * g M e b r θ)
  - sumIdx (fun e => Γtot M r θ e c b * g M a e r θ)
```

**Key observation**: Christoffel symbols are written as `Γtot M r θ e c a`, meaning the dummy index `e` is the **FIRST upper index**.

---

## 2. Expansion of `nabla_g M r θ ν ρ b`

When we call `nabla_g M r θ ν ρ b`:
- `c = ν`
- `a = ρ`
- `b = b`

The definition unfolds to:
```lean
dCoord ν (fun r θ => g M ρ b r θ) r θ
- sumIdx (fun e => Γtot M r θ e ν ρ * g M e b r θ)
- sumIdx (fun e => Γtot M r θ e ν b * g M ρ e r θ)
```

---

## 3. What Paul's Patch Expects (Lines 9008-9014)

```lean
have Hμ :
    nabla_g M r θ ν ρ b
      = dCoord ν (fun r θ => g M ρ b r θ) r θ
      - sumIdx (fun e => Γtot M r θ ρ ν e * g M e b r θ)
      - sumIdx (fun e => Γtot M r θ b ν e * g M ρ e r θ) := by
  simp [nabla_g, sub_eq_add_neg]
```

**Expected Christoffel symbols**:
- First sum: `Γtot M r θ ρ ν e` (ρ and ν are lower indices, e is last)
- Second sum: `Γtot M r θ b ν e` (b and ν are lower indices, e is last)

---

## 4. The Mismatch

| Component | Actual expansion from `nabla_g` | Expected by Paul's patch | Match? |
|-----------|--------------------------------|-------------------------|--------|
| First sum | `Γtot M r θ e ν ρ` | `Γtot M r θ ρ ν e` | ❌ NO |
| Second sum | `Γtot M r θ e ν b` | `Γtot M r θ b ν e` | ❌ NO |

The **index positions are completely different**!

---

## 5. Why `simp [nabla_g]` Fails

When Lean executes `simp [nabla_g]`, it:
1. Unfolds `nabla_g M r θ ν ρ b` to the LHS of the definition
2. Produces `Γtot M r θ e ν ρ` and `Γtot M r θ e ν b`
3. Compares to the goal RHS which expects `Γtot M r θ ρ ν e` and `Γtot M r θ b ν e`
4. **Cannot match** → unsolved goals

---

## 6. Root Cause Analysis

### Hypothesis A: Incorrect Patch

**Possibility**: Paul's patch has the wrong index convention.

**Evidence**: The actual `nabla_g` definition clearly uses `Γtot M r θ e c a` pattern.

**Likelihood**: **MEDIUM** - Paul may have assumed a different convention.

---

### Hypothesis B: Missing Symmetry Lemma

**Possibility**: There exists a symmetry lemma that relates:
- `Γtot M r θ e c a` ↔ `Γtot M r θ a c e`

**Evidence needed**: Search for Christoffel symmetry lemmas.

**Likelihood**: **HIGH** - Christoffel symbols have known symmetries.

---

### Hypothesis C: Wrong Function Call

**Possibility**: The code should call a different variant of `nabla_g` with different argument order.

**Evidence needed**: Search for other covariant derivative definitions.

**Likelihood**: **LOW** - There's only one `nabla_g` definition at line 3213.

---

## 7. Immediate Actions Required

### Action 1: Search for Christoffel Symmetry Lemmas ⭐ **URGENT**

```bash
grep -n "lemma.*Γtot.*symm\|Γtot.*comm" /Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean
```

Look for lemmas like:
- `Γtot M r θ e c a = Γtot M r θ a c e`
- `Γtot M r θ i j k = Γtot M r θ k j i` (or similar)

---

### Action 2: Ask Paul About Index Convention

**Questions for Paul**:
1. What is the correct index convention for `Γtot M r θ i j k`?
   - Is it `Γ^i_{jk}` or `Γ^k_{ij}`?
2. Is there a symmetry lemma relating different index orders?
3. Should the proof use a different expansion pattern?

---

### Action 3: Alternative - Manual Index Reordering

If no symmetry lemma exists, we could try:
1. Expand `nabla_g` with `simp [nabla_g]`
2. Manually rewrite the Christoffel indices using known symmetries
3. Use `conv` mode to reshape the terms

**Example**:
```lean
have Hμ :
    nabla_g M r θ ν ρ b
      = dCoord ν (fun r θ => g M ρ b r θ) r θ
      - sumIdx (fun e => Γtot M r θ ρ ν e * g M e b r θ)
      - sumIdx (fun e => Γtot M r θ b ν e * g M ρ e r θ) := by
  simp only [nabla_g, sub_eq_add_neg]
  -- Now we have Γtot M r θ e ν ρ but need Γtot M r θ ρ ν e
  conv_lhs => {
    -- Apply symmetry lemma to swap indices
    rw [some_christoffel_symmetry_lemma]
  }
```

---

## 8. Comparison with Previous Working Code

Let me check if there are other places in the file where `nabla_g` is successfully expanded:

**TODO**: Search for successful `nabla_g` expansions to see what pattern they use.

---

## 9. Technical Details

### Build Log
- **File**: `build_paul_nabla_fix_nov17.txt`
- **Errors**: 16 total (4 new + 12 pre-existing)

### Error Locations
| Line | Error Type | Component |
|------|-----------|-----------|
| 9012 | Unsolved goals | `Hμ` expansion |
| 9020 | Unsolved goals | `Hν` expansion |
| 9040 | `simp` failed | `Hpoint` (cascades from 9012/9020) |
| 9080 | Unsolved goals | Calc step (cascades) |

### Code Locations
- **`nabla_g` definition**: Riemann.lean:3213-3216
- **Paul's `Hμ` patch**: Riemann.lean:9008-9014
- **Paul's `Hν` patch**: Riemann.lean:9016-9022

---

## 10. Conclusion

Paul's surgical patch is **mathematically correct** in concept (the covariant derivative has two contractions), but uses the **wrong index convention** for this codebase's Christoffel symbol representation.

**Critical blocker**: Cannot proceed with Hshape implementation until we either:
1. Find the correct index convention/symmetry lemmas, OR
2. Get clarification from Paul about the intended approach

**Recommended action**:
1. **URGENT**: Search for Christoffel symmetry lemmas in the codebase
2. Report findings to Paul with specific questions about index conventions
3. Consider alternative: work with the actual `nabla_g` definition's index pattern instead of Paul's expected pattern

---

**Report Completed**: November 17, 2024
**Build Status**: 16 errors (regression from Paul's patch)
**Blocking Issue**: Index convention mismatch in Christoffel symbols
**Next Steps**: Search for symmetry lemmas or consult Paul
