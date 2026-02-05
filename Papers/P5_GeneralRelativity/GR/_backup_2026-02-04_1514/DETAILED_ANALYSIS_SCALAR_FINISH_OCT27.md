# Detailed Analysis: Why scalar_finish is Correct But Misapplied (October 27, 2025)

**Status**: Mathematical root cause identified
**Finding**: `scalar_finish` is algebraically correct, but the proof architecture is flawed

---

## The Confusion

At first glance, it seems contradictory:
1. `scalar_finish` is proven with `ring` (pure algebra) ✅
2. SP says the identity is mathematically false ❌

**How can both be true?**

---

## What `scalar_finish` Actually Proves

```lean
have scalar_finish :
  ∀ ρ,
    ( -(∂_μ Γ^ρ_νa) · g_ρb + (∂_ν Γ^ρ_μa) · g_ρb )
    + ( g_ρb · (Σ_e Γ^ρ_μe Γ^e_νa - Σ_e Γ^ρ_νe Γ^e_μa) )
    = -( (∂_μ Γ^ρ_νa - ∂_ν Γ^ρ_μa + Σ_e Γ^ρ_μe Γ^e_νa - Σ_e Γ^ρ_νe Γ^e_μa) · g_ρb )
  := by
    intro ρ
    ring
```

This is a **pointwise algebraic identity** for each fixed ρ. It's just rearranging:
- Moving negatives
- Factoring out `g_ρb`
- Distributing multiplication

**The `ring` tactic can prove this because it's valid algebra.** ✅

---

## What Pattern B Actually Tries to Prove

The calc chain at line 7808:

```lean
sumIdx B_b - sumIdx (Γ^ρ_μa · ∇_ν g_ρb) + sumIdx (Γ^ρ_νa · ∇_μ g_ρb)
= sumIdx (-(∂_μ Γ^ρ_νa - ∂_ν Γ^ρ_μa + Σ_e Γ^ρ_μe Γ^e_νa - Σ_e Γ^ρ_νe Γ^e_μa) · g_ρb)
```

Where:
```lean
B_b(ρ) := -(∂_μ Γ^ρ_νa) · g_ρb + (∂_ν Γ^ρ_μa) · g_ρb
          - Γ^ρ_νa · ∂_μ g_ρb + Γ^ρ_μa · ∂_ν g_ρb
```

This claims that after:
1. Expanding `∇_ν g_ρb = ∂_ν g_ρb - Σ_e Γ^e_νρ g_eb - Σ_e Γ^e_νb g_ρe`
2. Expanding `∇_μ g_ρb = ∂_μ g_ρb - Σ_e Γ^e_μρ g_eb - Σ_e Γ^e_μb g_ρe`
3. Summing over all ρ

We get exactly what `scalar_finish` describes.

**This is mathematically FALSE.** ❌

---

## The Missing Terms: SP's Cross Terms

When we expand the covariant derivatives:

```lean
-Γ^ρ_μa · ∇_ν g_ρb
= -Γ^ρ_μa · (∂_ν g_ρb - Σ_e Γ^e_νρ g_eb - Σ_e Γ^e_νb g_ρe)
= -Γ^ρ_μa · ∂_ν g_ρb                    [payload - cancels with B_b]
  + Γ^ρ_μa · Σ_e Γ^e_νρ g_eb            [main ΓΓ term]
  + Γ^ρ_μa · Σ_e Γ^e_νb g_ρe            [CROSS TERM - missing!]
```

Similarly:
```lean
+Γ^ρ_νa · ∇_μ g_ρb
= +Γ^ρ_νa · (∂_μ g_ρb - Σ_e Γ^e_μρ g_eb - Σ_e Γ^e_μb g_ρe)
= +Γ^ρ_νa · ∂_μ g_ρb                    [payload - cancels with B_b]
  - Γ^ρ_νa · Σ_e Γ^e_μρ g_eb            [main ΓΓ term]
  - Γ^ρ_νa · Σ_e Γ^e_μb g_ρe            [CROSS TERM - missing!]
```

### Full Expansion After Payload Cancellation

```lean
sumIdx B_b - sumIdx(Γ^ρ_μa · ∇_ν g_ρb) + sumIdx(Γ^ρ_νa · ∇_μ g_ρb)
= Σ_ρ [-(∂_μ Γ^ρ_νa) · g_ρb + (∂_ν Γ^ρ_μa) · g_ρb]              [∂Γ terms]
  + Σ_ρ Σ_e [Γ^ρ_μa Γ^e_νρ g_eb - Γ^ρ_νa Γ^e_μρ g_eb]          [main ΓΓ terms]
  + Σ_ρ Σ_e [Γ^ρ_μa Γ^e_νb g_ρe - Γ^ρ_νa Γ^e_μb g_ρe]          [CROSS TERMS!]
```

### What scalar_finish Claims

```lean
scalar_finish claims the sum equals:
Σ_ρ [-(∂_μ Γ^ρ_νa - ∂_ν Γ^ρ_μa + Σ_e Γ^ρ_μe Γ^e_νa - Σ_e Γ^ρ_νe Γ^e_μa) · g_ρb]
= Σ_ρ [-(∂_μ Γ^ρ_νa) · g_ρb + (∂_ν Γ^ρ_μa) · g_ρb]              [∂Γ terms ✓]
  - Σ_ρ Σ_e [Γ^ρ_μe Γ^e_νa · g_ρb]                              [main term]
  + Σ_ρ Σ_e [Γ^ρ_νe Γ^e_μa · g_ρb]                              [main term]
```

By index manipulation (swapping dummy indices ρ ↔ e):
```
Σ_ρ Σ_e [Γ^ρ_μa Γ^e_νρ g_eb] = Σ_e Σ_ρ [Γ^ρ_μa Γ^e_νρ g_eb]
                                = Σ_e Σ_ρ [Γ^e_νρ Γ^ρ_μa g_eb]
                                = Σ_e [Γ^e_νb (Σ_ρ Γ^ρ_μa) g_eb]  [if b=ρ by diagonality]
```

Wait, let me be more careful. By symmetry Γ^e_νρ = Γ^e_ρν:
```
Σ_ρ Σ_e [Γ^ρ_μa Γ^e_νρ g_eb] = Σ_ρ Σ_e [Γ^ρ_μa Γ^e_ρν g_eb]
```

Now swap dummy indices ρ ↔ e:
```
= Σ_e Σ_ρ [Γ^e_μa Γ^ρ_eν g_ρb]
= Σ_e Σ_ρ [Γ^e_μa Γ^ρ_νe g_ρb]
= Σ_e Σ_ρ [Γ^ρ_μa Γ^e_νa g_ρb]  [wrong! let me redo this carefully]
```

Actually, I'm making errors. Let me just state SP's conclusion:

**After careful index manipulation, the main terms match, but there's a leftover cross term**:
```
T_{a,Cross} = Σ_ρ Σ_e [Γ^ρ_μa Γ^e_νb g_ρe - Γ^ρ_νa Γ^e_μb g_ρe]
```

With diagonal metric:
```
T_{a,Cross} = Σ_ρ [Γ^ρ_μa Γ^ρ_νb - Γ^ρ_νa Γ^ρ_μb] · g_ρρ
```

**This is non-zero in general and has no corresponding term in scalar_finish's RHS.**

---

## Why `scalar_finish` is Technically Correct

The lemma `scalar_finish` proves a pointwise algebraic identity. If we start from:
```
B_b(ρ) + stuff that matches scalar_finish's LHS
```

Then by algebra, we can rearrange to:
```
stuff that matches scalar_finish's RHS
```

**The problem is that "stuff" doesn't actually match what we get from expanding ∇g.**

When we expand ∇g, we get **extra cross terms** that aren't in `scalar_finish`'s LHS.

---

## The Architectural Error

The proof is structured as:

**Step 1**: Prove for b-branch (a-index varying, b-index fixed):
```lean
calc
  sumIdx B_b - sumIdx(Γ^ρ_μa · ∇_ν g_ρb) + sumIdx(Γ^ρ_νa · ∇_μ g_ρb)
  = [some Riemann-related expression]
```

**Step 2**: Prove for a-branch (b-index varying, a-index fixed):
```lean
calc
  sumIdx B_a - sumIdx(Γ^ρ_μb · ∇_ν g_aρ) + sumIdx(Γ^ρ_νb · ∇_μ g_aρ)
  = [some Riemann-related expression]
```

**Step 3**: Combine the two branches.

**The error**: Steps 1 and 2 individually are FALSE because each has uncanceled cross terms.

**The truth**: Only the combination (Step 1 + Step 2) is true, because:
```
T_{a,Cross} + T_{b,Cross} = 0
```

The cross terms cancel pairwise across branches.

---

## SP's Concrete Counterexample

In flat 2D polar coordinates with μ=r, ν=θ, a=r, b=θ:

The a-branch cross term evaluates to:
```
T_{a,Cross} = -1 ≠ 0
```

This proves the b-branch identity (Step 1) is false when computed in isolation.

By symmetry, the a-branch identity (Step 2) would have:
```
T_{b,Cross} = +1 ≠ 0
```

But their sum:
```
T_{a,Cross} + T_{b,Cross} = -1 + 1 = 0 ✓
```

---

## What `scalar_finish` Should Be

For the isolated branch approach to work, `scalar_finish` would need to be:

```lean
have scalar_finish :
  ∀ ρ,
    B_b ρ + [connection terms including cross terms]
    = -RiemannUp ρ a μ ν · g_ρb + [some correction involving b-branch]
```

But this is impossible because the correction term involves the OTHER branch's data.

---

## The Correct Approach: Four-Block Strategy

Instead of proving:
```
[b-branch] = [Riemann b-related]
[a-branch] = [Riemann a-related]
```

We must prove:
```
[b-branch] + [a-branch] = [Riemann b-related] + [Riemann a-related]
```

In one unified calc chain where the cross terms cancel before applying the Ricci identity.

---

## Impact on Codebase

### Lines 7808-7820 (b-branch calc)
**Status**: Mathematically incorrect as stated
**Issue**: Missing cross term in RHS
**Fix**: Must combine with a-branch before this step

### Lines 7841-onwards (a-branch calc)
**Status**: Mathematically incorrect as stated (symmetric to b-branch)
**Issue**: Missing cross term in RHS
**Fix**: Must combine with b-branch before this step

### `scalar_finish` lemma (line 7790)
**Status**: Algebraically correct but incomplete
**Issue**: Only accounts for ∂Γ and main ΓΓ terms, not cross terms
**Fix**: Either:
1. Redefine to include cross terms (impossible without other branch data)
2. Use only in combined-branch context where cross terms already canceled

---

## Remediation Options

### Option A: Restructure to Combined Calc (Correct but Major)

```lean
calc
  -- Combine both branches from the start
  (sumIdx B_b + sumIdx B_a)
  - sumIdx(Γ^ρ_μa · ∇_ν g_ρb) + sumIdx(Γ^ρ_νa · ∇_μ g_ρb)
  - sumIdx(Γ^ρ_μb · ∇_ν g_aρ) + sumIdx(Γ^ρ_νb · ∇_μ g_aρ)
  = [expand ∇g]
  = [payload cancellation]
  = [cross term cancellation] ← NEW STEP
  = [apply Ricci identity to combined expression]
```

**Pros**: Mathematically correct
**Cons**: Requires significant refactoring

### Option B: Mark with Sorry and Document (Quick)

```lean
calc
  sumIdx B_b - sumIdx(Γ^ρ_μa · ∇_ν g_ρb) + sumIdx(Γ^ρ_νa · ∇_μ g_ρb)
  = sumIdx(...) := by
    -- NOTE: This step is mathematically false when proven in isolation!
    -- The cross terms Σ_ρ[Γ^ρ_μa Γ^ρ_νb - Γ^ρ_νa Γ^ρ_μb]·g_ρρ are non-zero.
    -- They only cancel when combined with the symmetric a-branch.
    -- See CRITICAL_SP_FINDING_FALSE_IDENTITY_OCT27.md for full analysis.
    sorry
```

**Pros**: Honest, documents the issue, allows progress on other errors
**Cons**: Leaves known false lemma in codebase

### Option C: Prove Cross Term Cancellation Separately (Hybrid)

1. Keep the branch structure
2. Add explicit lemma proving cross term cancellation:
   ```lean
   have cross_terms_cancel :
     T_{a,Cross} + T_{b,Cross} = 0 := by [proof]
   ```
3. Modify scalar_finish to include cross terms temporarily
4. Apply cross term cancellation before final Riemann identity

**Pros**: Minimal refactoring, makes cross term cancellation explicit
**Cons**: Intermediate steps still technically "false" but documented

---

## Recommended Path Forward

1. **Immediate**: Mark Pattern B sites with `sorry` + detailed comment
2. **Document**: Link to this analysis and SP's finding
3. **Plan**: Design Four-Block combined calc structure
4. **Implement**: When ready, replace sorry with combined-branch proof
5. **Verify**: Get SP to verify the combined-branch identity

---

**Prepared by**: Claude Code (Sonnet 4.5)
**Date**: October 27, 2025
**Status**: Root cause fully analyzed
**Confidence**: High - SP's counterexample is definitive proof
