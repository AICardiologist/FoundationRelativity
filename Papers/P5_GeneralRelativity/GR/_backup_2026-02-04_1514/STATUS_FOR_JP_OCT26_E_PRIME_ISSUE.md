# Status Update for JP: E' Integration Issue - October 26, 2025

**Status**: ⚠️ **BLOCKED** on E' proof - need guidance on bridging expand_P_ab output to dG_b + dG_a form

---

## What Worked ✅

1. **Abbrev integration**: ✅ SUCCESS
   - Renamed Unicode names (`Γμ⋅∇ν` → `Gamma_mu_nabla_nu`)
   - Type signature elaboration now instant (was timing out)

2. **Four auxiliary definitions**: ✅ Pasted successfully
   - `dG_b`, `dG_a`, `P_b`, `P_a` all compile
   - Lines 7082-7093

3. **Calc chain structure**: ✅ Syntax correct
   - All subsequent calc steps compile fine (when we skip the first step with `sorry`)

---

## What's Blocked ❌

**Line 7107**: First calc step in E' proof

```lean
have E' :
  (dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ
   - dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ)
  = sumIdx B_b + sumIdx B_a := by
  calc
    (dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ
     - dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ)
        = sumIdx (fun ρ => dG_b ρ + dG_a ρ)
        + sumIdx (fun ρ => P_b ρ + P_a ρ) := by
          -- JP's original: simpa [dG_b, dG_a, P_b, P_a] using E
          ???  -- BLOCKED HERE
```

---

## The Core Issue

**What `E` provides** (from `expand_P_ab`):
```lean
E : (dCoord μ (nabla_g ν a b) - dCoord ν (nabla_g μ a b))
  = (sumIdx (fun e =>
       -(∂_μ Γ^e_νa) * g_eb + (∂_ν Γ^e_μa) * g_eb   -- both a and b terms
       -(∂_μ Γ^e_νb) * g_ae + (∂_ν Γ^e_μb) * g_ae))
  + (sumIdx (fun e =>
       -(Γ^e_νa) * (∂_μ g_eb) + (Γ^e_μa) * (∂_ν g_eb)   -- both a and b terms
       -(Γ^e_νb) * (∂_μ g_ae) + (Γ^e_μb) * (∂_ν g_ae)))
```

**What we need**:
```lean
sumIdx (fun ρ => dG_b ρ + dG_a ρ) + sumIdx (fun ρ => P_b ρ + P_a ρ)
```

**Where**:
```lean
dG_b ρ = -(∂_μ Γ^ρ_νa) * g_ρb + (∂_ν Γ^ρ_μa) * g_ρb
dG_a ρ = -(∂_μ Γ^ρ_νb) * g_aρ + (∂_ν Γ^ρ_μb) * g_aρ
P_b  ρ = -(Γ^ρ_νa) * (∂_μ g_ρb) + (Γ^ρ_μa) * (∂_ν g_ρb)
P_a  ρ = -(Γ^ρ_νb) * (∂_μ g_aρ) + (Γ^ρ_μb) * (∂_ν g_aρ)
```

---

## What We Tried

### Attempt 1: Original `simpa` approach
```lean
simpa [dG_b, dG_a, P_b, P_a] using E
```

**Error**:
```
error: Type mismatch: After simplification, term E has type
  [expand_P_ab's RHS with fully expanded nabla_g definition]
but is expected to have type
  sumIdx (fun ρ => dG_b ρ + dG_a ρ) + sumIdx (fun ρ => P_b ρ + P_a ρ)
```

**Diagnosis**: `simpa` unfolds `nabla_g` in E's type, making it too complex to match.

### Attempt 2: `convert` with goals
```lean
convert E using 2
· apply sumIdx_congr; intro ρ; simp [dG_b, dG_a]
· apply sumIdx_congr; intro ρ; simp [P_b, P_a]
```

**Error**: Unsolved goals in both branches

### Attempt 3: Explicit calc with E first
```lean
calc
  LHS = (sumIdx (fun e => [expand_P_ab's first sum])) +
        (sumIdx (fun e => [expand_P_ab's second sum])) := E
  _   = sumIdx (fun ρ => dG_b ρ + dG_a ρ) +
        sumIdx (fun ρ => P_b ρ + P_a ρ) := by
          simp only [dG_b, dG_a, P_b, P_a]
```

**Error**: Unsolved goals - `simp only` doesn't complete the match

### Attempt 4: Direct `rfl`
```lean
... := rfl
```

**Error**: Type mismatch - not definitionally equal despite being mathematically equal

---

## Analysis

The mathematical claim is **correct**:
```
sumIdx (fun e => (a_terms_for_e + b_terms_for_e))
  = sumIdx (fun ρ => a_terms_for_ρ) + sumIdx (fun ρ => b_terms_for_ρ)
```

This is just regrouping sum terms.

But Lean isn't seeing them as syntactically equal because:
1. Bound variable names differ (`e` vs `ρ`)
2. The grouping inside the sumIdx is different
3. Need explicit proof that they're equal, not just simplification

---

## Question for JP

**How do we bridge from `E` (expand_P_ab's output) to the form with `dG_b + dG_a` and `P_b + P_a`?**

Specifically:
- Should we prove an explicit lemma that shows the regrouping?
- Is there a tactic we're missing that would make `simpa [dG_b, dG_a, P_b, P_a] using E` work?
- Do we need to first rewrite `E` to match the bound variable names?
- Should we use a different approach entirely?

---

## Context

**File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`

**Location**: Lines 7097-7122 (E' proof)

**Build log**: `/tmp/build_rfl.txt`

**Current error** (line 7121):
```
error: Type mismatch
  rfl
has type
  ?m.532 = ?m.532
but is expected to have type
  ((sumIdx fun e => ...) + (sumIdx fun e => ...)) =
  ((sumIdx fun ρ => dG_b ρ + dG_a ρ) + (sumIdx fun ρ => P_b ρ + P_a ρ))
```

---

## What's Available

Available lemmas in codebase:
- `sumIdx_add_distrib : sumIdx (f + g) = sumIdx f + sumIdx g`
- `sumIdx_congr : (∀ i, f i = g i) → sumIdx f = sumIdx g`

These should be sufficient mathematically, but we need the right tactical approach to connect them.

---

## Next Steps

⏳ **AWAITING JP GUIDANCE** on how to prove the first calc step in E'.

Once we get past line 7107, the rest of the calc chain should work (all subsequent steps compile when we replace this step with `sorry`).

---

**Date**: October 26, 2025
**Agent**: Claude Code (Sonnet 4.5)
**For**: JP (Tactic Professor)

---
