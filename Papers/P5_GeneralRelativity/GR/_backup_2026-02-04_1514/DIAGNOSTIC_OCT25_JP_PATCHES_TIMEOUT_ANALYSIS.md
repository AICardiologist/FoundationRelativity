# Diagnostic Report: JP's Drop-In Patches - Timeout Analysis

**Date**: October 25, 2025
**Status**: ❌ **COMPILATION FAILED**
**Issue**: Deterministic timeouts in type-checking and tactic execution

---

## Executive Summary

JP's drop-in patches for `algebraic_identity`, `ricci_identity_on_g_general`, and `Riemann_swap_a_b_ext` **fail to compile** with multiple deterministic timeout errors. The root cause is that **complex `let` expressions in type signatures** cause Lean 4 to timeout during type elaboration.

**Critical Finding**: The lemma signature itself (line 7021-7045) causes an `isDefEq` timeout **before any tactics execute**. This indicates a fundamental issue with how the lemma is stated, not just the proof tactics.

---

## Timeout Locations

### 1. Type Signature Timeout (Line 7021) - **MOST CRITICAL**

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:7021:0:
(deterministic) timeout at `isDefEq`,
maximum number of heartbeats (200000) has been reached
```

**Location**: The `lemma algebraic_identity_jp` signature itself

**What this means**:
- Lean is timing out while checking if the **type** is well-formed
- The `let` expressions in the type signature create a complex dependent type
- Lean cannot determine definitional equality (`isDefEq`) within 200000 heartbeats
- **This happens BEFORE any proof tactics run**

**The problematic type signature**:
```lean
lemma algebraic_identity_jp
  (M r θ : ℝ) (h_ext : Exterior M r θ) (hθ : Real.sin θ ≠ 0)
  (μ ν a b : Idx) :
  (let Gamma_mu_nabla_nu : ℝ :=
        sumIdx (fun ρ =>
          (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b)
        + (Γtot M r θ ρ μ b) * (nabla_g M r θ ν a ρ));
   let Gamma_nu_nabla_mu : ℝ :=
        sumIdx (fun ρ =>
          (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b)
        + (Γtot M r θ ρ ν b) * (nabla_g M r θ μ a ρ));
   ((dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ - Gamma_mu_nabla_nu)
  - (dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ - Gamma_nu_nabla_mu)))
=
  - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
  - sumIdx (fun ρ => RiemannUp M r θ ρ b μ ν * g M a ρ r θ)
```

**Root cause**: The nested `let` expressions with `sumIdx` over complex lambda expressions create a type that's too expensive to normalize.

### 2. Tactic Execution Timeout (Line 7162)

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:7162:8:
(deterministic) timeout at `«tactic execution»`,
maximum number of heartbeats (200000) has been reached
```

**Location**: Inside the calc chain, at `rw [b_branch, a_branch]`

**What this means**:
- Even if the type signature compiled, the proof tactics would timeout
- The rewrite of `b_branch` and `a_branch` requires unfolding `B_b`, `B_a`, `nabla_g`, etc.
- Lean times out trying to match and rewrite these complex expressions

### 3. Ring Tactic Timeout (Line 7165)

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:7165:70:
(deterministic) timeout at `«tactic execution»`,
maximum number of heartbeats (200000) has been reached
```

**Location**: Final `ring` call in the calc chain

**What this means**:
- The `ring` tactic is trying to prove equality of two very large polynomial expressions
- With all the sum terms expanded, the expression is too large for `ring` to normalize

---

## Additional Compilation Errors

### Rewrite Pattern Not Found (Lines 7096, 7112, 7134)

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:7096:14:
Tactic `rewrite` failed: Did not find an occurrence of the pattern
```

**Location**: In the `E'` proof, trying to rewrite with `expand_P_ab`

**What this means**:
- The pattern from `expand_P_ab` doesn't match what we're trying to rewrite
- Suggests a type mismatch or index ordering issue between `expand_P_ab` output and `algebraic_identity` LHS

### Kernel Error in ricci_identity_on_g_jp (Line 7174)

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:7174:6:
(kernel) unknown constant 'Papers.P5_GeneralRelativity.Schwarzschild.algebraic_identity_jp'
```

**What this means**:
- `ricci_identity_on_g_jp` tries to reference `algebraic_identity_jp`
- But `algebraic_identity_jp` failed to compile (due to timeout)
- So Lean doesn't know what `algebraic_identity_jp` is

**This is a cascading failure**: Fix `algebraic_identity_jp` and this error disappears.

### Unsolved Goals in Riemann_swap_a_b_ext (Lines 7532, 7555, 7559)

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:7559:4:
unsolved goals
```

**What this means**:
- `Riemann_swap_a_b_ext` depends on `ricci_identity_on_g_jp`
- Which depends on `algebraic_identity_jp`
- Since both failed, `Riemann_swap_a_b_ext` can't compile

**This is also a cascading failure**: Fix the upstream lemmas and this should resolve.

---

## Root Cause Analysis

### Why are we getting timeouts?

**Primary Cause**: **Complex let-expressions in type signatures**

Lean 4's type-checker has to normalize types to check definitional equality. When you put `let` expressions with complex lambda terms and `sumIdx` operations in the **type signature** (not the proof body), Lean has to:

1. Normalize all the let-bindings
2. Expand all the lambda terms
3. Unfold `sumIdx`, `nabla_g`, `Γtot`, etc.
4. Check if the resulting expressions are definitionally equal

For expressions this complex, this process exceeds 200000 heartbeats.

**Secondary Cause**: **Unbounded simpa/ring in calc chains**

Even if the type signature compiled, the proof uses:
- `simpa [reshape, E']` at line 7149
- `simp [hCμ, hCν, ...]` at line 7157
- `ring` at lines 7158, 7165

These tactics operate on very large expressions with many terms. When Lean tries to normalize them, it times out.

**Tertiary Cause**: **Pattern mismatch between expand_P_ab and algebraic_identity**

The output of `expand_P_ab` doesn't directly match the LHS of `algebraic_identity`. There's likely an index ordering or type mismatch that prevents direct rewriting.

---

## Attempted Fixes and Why They Failed

### Fix Attempt 1: Change `set ... := rfl` to `let` bindings

**Rationale**: `set ... := rfl` doesn't exist in Lean 4, so use `let` instead

**Result**: ❌ FAILED - This fixed the syntax error but introduced the timeout issue

**Why**: `let` bindings in type signatures are even more expensive than in proof bodies

### Fix Attempt 2: Unfold B_b/B_a before sumIdx_add_distrib

**Rationale**: Make the pattern more explicit so Lean can find it

**Result**: ❌ FAILED - Rewrite still doesn't find the pattern

**Why**: The issue is deeper - the types don't match

### Fix Attempt 3: Use explicit `simp only` lists

**Rationale**: Avoid unbounded `simp`

**Result**: ⚠️ PARTIAL - Helps in some places, but doesn't solve timeouts

**Why**: The expressions are still too large

---

## Comparison with expand_P_ab (Which WORKS)

**expand_P_ab** successfully compiles with 0 sorries. Why doesn't it have the same timeout issues?

### Key Differences:

1. **No let-expressions in type signature**
   - expand_P_ab states the conclusion directly
   - No nested `let` bindings that need normalization

2. **Bounded tactics throughout**
   - Uses explicit `rw [specific_lemma]`
   - Uses `simp only [explicit_list]` (not unbounded `simp`)
   - Uses `ring` only under `intro ρ` (scalar context, not sum context)

3. **Explicit intermediate steps**
   - Breaks the proof into named lemmas (H_b, H_a, H_b', H_a', etc.)
   - Each step is small and checkable
   - No large calc chains with complex expressions

### What expand_P_ab does RIGHT:

```lean
-- Define transformations explicitly with let (in PROOF BODY, not signature)
let Fb : Idx → ℝ := fun ρ => ...
let Fa : Idx → ℝ := fun ρ => ...
let D : Idx → ℝ := fun ρ => ...
let P : Idx → ℝ := fun ρ => ...

-- Build intermediate equality
have restructure :
    sumIdx Fb + sumIdx Fa = sumIdx D + sumIdx P := by
  rw [← sumIdx_add_distrib]
  have regroup : sumIdx (fun ρ => Fb ρ + Fa ρ) = sumIdx (fun ρ => D ρ + P ρ) := by
    apply sumIdx_congr
    intro ρ
    simp only [Fb, Fa, D, P, <explicit algebra lemmas>]
    ring  -- ← ring on SCALAR, not on sums!
  rw [regroup, sumIdx_add_distrib]

-- Use the intermediate result
simp only [Fb, Fa, D, P] at restructure
exact restructure
```

**Key insight**: `ring` is called under `intro ρ`, so it operates on **scalar expressions**, not sums. This is fast and deterministic.

### What algebraic_identity_jp does WRONG:

```lean
-- let-expressions in TYPE SIGNATURE (BAD!)
lemma algebraic_identity_jp ... :
  (let Gamma_mu_nabla_nu := ... in ...)  -- ← Timeout during type-checking

-- Unbounded simpa on large expressions
_ = ... := by
  simpa [reshape, E']  -- ← Tries to simplify huge expression

-- ring on sums (not scalars)
_ = ... := by
  simp [...]
  ring  -- ← Operating on sum-level, very expensive
```

---

## Potential Solutions

### Solution 1: Reformulate without let-expressions in type signature

**Instead of**:
```lean
lemma algebraic_identity_jp ... :
  (let X := ... in
   let Y := ... in
   (... - X) - (... - Y))
= ...
```

**Use**:
```lean
def Gamma_mu_nabla_nu (M r θ : ℝ) (μ a b : Idx) : ℝ :=
  sumIdx (fun ρ => ...)

lemma algebraic_identity_jp ... :
  ((... - Gamma_mu_nabla_nu M r θ μ a b)
 - (... - Gamma_nu_nabla_mu M r θ ν a b))
= ...
```

**Move the definitions outside the lemma**, then reference them in the type.

### Solution 2: Break into smaller lemmas

**Instead of**: One large `algebraic_identity` with complex calc chain

**Use**:
```lean
lemma payload_terms_cancel : (P_payload + C_payload) = 0
lemma dGamma_terms_match : (dGamma_from_P + dGamma_from_C) = RiemannUp * g
lemma algebraic_identity : ... := by
  rw [expand_P_ab]
  rw [payload_terms_cancel]
  rw [dGamma_terms_match]
  ring
```

**Each small lemma** can be proven independently and is fast to check.

### Solution 3: Use expand_P_ab's pattern

**Model the proof after expand_P_ab**:
- Define transformations with `let` in proof body
- Use `sumIdx_congr` to work pointwise
- Call `ring` only on scalars (under `intro ρ`)
- Build explicit intermediate equalities
- Assemble with simple rewrites

### Solution 4: Abandon this approach entirely

If the mathematical connection between `expand_P_ab` and `algebraic_identity` isn't direct (which the pattern-match errors suggest), we may need a different proof strategy altogether.

**Wait for SP's mathematical verification** before spending more time on this approach.

---

## Consultation Status

**Created**: `CONSULT_TO_SP_OCT25_RICCI_IDENTITY_MATH_CHECK.md`

**Questions for SP**:
1. Is the mathematical statement of `algebraic_identity_jp` correct?
2. Does it follow directly from `expand_P_ab`?
3. Is the index handling (`g_ρb` vs `g_bρ`) correct?
4. Is there a simpler formulation?

**Awaiting**: SP's mathematical verification before proceeding with further debugging.

---

## Recommendations

###  Immediate Actions:

1. **DO NOT COMMIT** the current broken code
2. **WAIT** for SP's mathematical verification
3. **REVERT** to last working state (expand_P_ab complete, new lemmas removed)

### If Math is Verified:

4. **Reformulate** lemmas without let-expressions in type signatures
5. **Break down** proofs into smaller, named intermediate lemmas
6. **Model** proof structure after expand_P_ab's successful pattern
7. **Test incrementally** - compile each small piece before assembling

### If Math Needs Revision:

8. **Work with SP** to get correct mathematical statements
9. **Work with JP** to get tactics that match the correct math
10. **Restart** with corrected approach

---

## Technical Details for JP

### Heartbeat Limits Hit:

- **200000 heartbeats** is the default deterministic timeout
- We're hitting this at:
  - Type elaboration (`isDefEq`)
  - Tactic execution (`rw`, `ring`)
  - Simplification (`simp`, `simpa`)

### Why Bounded Tactics Matter:

expand_P_ab succeeds because:
- `ring` called only on scalars (under `intro ρ`)
- `simp only [explicit_list]` - no search
- No complex calc chains - explicit intermediate steps

algebraic_identity_jp fails because:
- `ring` called on sum-level expressions (exponential blowup)
- `simpa [...]` with implicit simp set (unbounded search)
- Long calc chains with complex normalization

### Suggested Tactic Pattern:

```lean
have step1 : A = B := by
  rw [← sumIdx_add_distrib]
  apply sumIdx_congr
  intro ρ
  simp only [explicit, list, of, lemmas]
  ring  -- ← On scalar, fast!

have step2 : B = C := by
  rw [step1]
  simp only [more, explicit, lemmas]

-- Assemble
rw [step1, step2]
```

**NOT**:
```lean
calc
  A = B := by simpa [complex, implicit, stuff]
  _ = C := by simp [...]; ring  -- ← On sums, timeout!
```

---

## Files Status

### Successfully Compiled (✅):
- `expand_P_ab` (lines 6599-7017) - 0 sorries
- `nabla_g_zero_ext` (line 4057) - metric compatibility
- `dCoord_nabla_g_zero_ext` (line 4144) - derivative of ∇g

### Failed Compilation (❌):
- `algebraic_identity_jp` (lines 7030-7165) - TIMEOUT in type signature
- `ricci_identity_on_g_jp` (lines 7156-7210) - Depends on above
- `Riemann_swap_a_b_ext` (lines 7512-7617) - Depends on above

### Total Errors:
- 15 errors total
- 4 timeouts (3 deterministic timeout, 1 whnf timeout)
- 4 pattern match failures
- 4 unsolved goals (cascading from timeouts)
- 3 other errors

---

## Next Steps

1. ✅ **DONE**: Write consultation request to SP
2. ✅ **DONE**: Write diagnostic report (this document)
3. ⏳ **WAITING**: SP mathematical verification
4. ⏳ **PENDING**: Revert or reformulate based on SP feedback
5. ⏳ **PENDING**: Work with JP on bounded-tactics approach

---

**Bottom Line**: JP's patches are mathematically sophisticated but exceed Lean 4's type-checking and normalization capacity. We need either (a) reformulation to simpler types, or (b) verification that we're proving the right thing before investing more time in tactical fixes.

---

**Status**: ❌ **BLOCKED** - Awaiting SP mathematical verification

**Date**: October 25, 2025

---
