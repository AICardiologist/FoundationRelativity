# Diagnostic: JP's Drop-in Solution - Pattern Mismatch

**Date**: October 30, 2025
**File**: Riemann.lean lines 9150-9214
**Status**: ❌ **BUILD FAILED** - 25 errors (increased from 24 baseline)
**Build log**: `build_jp_dropin_solution_oct30.txt`

---

## Executive Summary

JP's drop-in solution was pasted verbatim at lines 9150-9214, but the build reveals a **fundamental pattern mismatch** between:
1. What JP's code expects (payload terms in form `Γtot * dCoord(g)`)
2. What the goal actually contains after Step 1-4 expansion

**Two specific errors at Riemann.lean:9204 and 9208** indicate the goal state differs from JP's assumptions.

---

## Error 1: Line 9204 - `payload_cancel_all` Type Mismatch

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9204:4: Type mismatch: After simplification, term
  payload_cancel_all M r θ h_ext μ ν a b
 has type
  ((sumIdx fun i => -(dCoord μ (fun r θ => g M b i r θ) r θ * Γtot M r θ i ν a)) +
            sumIdx fun i => dCoord ν (fun r θ => g M b i r θ) r θ * Γtot M r θ i μ a) +
          ((sumIdx fun i => -(dCoord ν (fun r θ => g M b i r θ) r θ * Γtot M r θ i μ a)) +
            sumIdx fun i => dCoord μ (fun r θ => g M b i r θ) r θ * Γtot M r θ i ν a) +
        ((sumIdx fun i => -(dCoord μ (fun r θ => g M a i r θ) r θ * Γtot M r θ i ν b)) +
          sumIdx fun i => dCoord ν (fun r θ => g M a i r θ) r θ * Γtot M r θ i μ b) +
      ((sumIdx fun i => -(dCoord ν (fun r θ => g M a i r θ) r θ * Γtot M r θ i μ b)) +
        sumIdx fun i => dCoord μ (fun r θ => g M a i r θ) r θ * Γtot M r θ i ν b) =
    0
but is expected to have type
  sumIdx f₁ + sumIdx f₂ + sumIdx f₃ + sumIdx f₄ = 0
```

### Analysis

**`payload_cancel_all` proves**:
Pattern: `dCoord(g) * Γtot` (metric derivative first)

**JP's f₁-f₄ definitions expect**:
Pattern: `Γtot * dCoord(g)` (Christoffel symbol first)

These are mathematically equal but **syntactically different**. The `simpa [hPdef]` fails because the term order doesn't match.

---

## Error 2: Line 9208 - Pattern Not Found in Goal

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9208:6: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  sumIdx fun e => Pe e
in the target expression
  ((sumIdx fun e =>
            -dCoord μ (fun r θ => Γtot M r θ e ν a) r θ * g M e b r θ -
                  dCoord μ (fun r θ => Γtot M r θ e ν b) r θ * g M a e r θ +
                dCoord ν (fun r θ => Γtot M r θ e μ a) r θ * g M e b r θ +
              dCoord ν (fun r θ => Γtot M r θ e μ b) r θ * g M a e r θ) +
```

### Analysis

**JP's `Pe` definition** (line 9166):
```lean
let Pe : Idx → ℝ := fun e => f₁ e + f₂ e + f₃ e + f₄ e
```
where each `fᵢ` has form `Γtot * dCoord(g)`

**Actual goal state** (from error):
The single sumIdx over `e` contains:
```lean
-dCoord μ (fun r θ => Γtot M r θ e ν a) r θ * g M e b r θ
-dCoord μ (fun r θ => Γtot M r θ e ν b) r θ * g M a e r θ
+dCoord ν (fun r θ => Γtot M r θ e μ a) r θ * g M e b r θ
+dCoord ν (fun r θ => Γtot M r θ e μ b) r θ * g M a e r θ
```

**Two critical issues**:

1. **Form**: Goal has `dCoord(Γtot) * g` — this is the **∂Γ block** (Christoffel derivative), NOT the payload!
2. **Missing payload**: The actual payload (`Γtot * dCoord(g)`) appears to be in a DIFFERENT sumIdx, possibly the second block from build_four_block_assembly_oct30.txt

---

## Root Cause: Goal Structure Mismatch

From `build_four_block_assembly_oct30.txt` lines 4122-4145, the goal after steps 1-4 has **THREE distinct sumIdx blocks**:

### Block 1: ∂Γ Terms (Index `e`)
```lean
sumIdx fun e =>
  -dCoord μ (fun r θ => Γtot M r θ e ν a) r θ * g M e b r θ +
        dCoord ν (fun r θ => Γtot M r θ e μ a) r θ * g M e b r θ -
      dCoord μ (fun r θ => Γtot M r θ e ν b) r θ * g M a e r θ +
    dCoord ν (fun r θ => Γtot M r θ e μ b) r θ * g M a e r θ
```
**Role**: Christoffel derivative terms (`dCoord(Γtot) * g`)
**Status**: This is what JP's code is trying to match, but it's NOT the payload!

### Block 2: **ACTUAL PAYLOAD** (Index `e`)  ⭐
```lean
sumIdx fun e =>
  -Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ +
        Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ -
      Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ +
    Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ
```
**Role**: The 4 payload terms (combined into one sumIdx)
**Index**: `e` (needs α-rename to `ρ`)
**Status**: THIS is what should match JP's f₁-f₄, but it's the SECOND sumIdx in the goal!

### Block 3: ΓΓ Terms
```lean
sumIdx fun ρ => ... (double products)
```
**Role**: Double-Christoffel products

---

## The Problem

JP's code assumes the **first (or only) sumIdx over `e`** contains the payload terms. But in the actual goal:
- **First sumIdx over `e`**: ∂Γ block (`dCoord(Γtot) * g`)
- **Second sumIdx over `e`**: Payload block (`Γtot * dCoord(g)`) ← THIS is what JP's code needs to match!

The `rw [h_payload_split]` at line 9208 searches for `sumIdx fun e => Pe e` but finds the ∂Γ block first, which has a completely different structure.

---

## What JP's Code Needs

**From JP's quote** (in his drop-in solution message):
> "After Steps 1–4 the LHS is:
> (∂Γ block over e)
> + (payload block over e) ← split this one only
> + (ΓΓ double-sum blocks over ρ,e)"

**What we need to tell JP**:

1. **Goal structure after line 9148** (`simp only [flatten₄₁, ...]`):
   - Block 1 (∂Γ): `sumIdx fun e => -dCoord μ (Γtot e ν a) * g e b + ...` (4 terms)
   - Block 2 (Payload): `sumIdx fun e => -Γtot e ν a * dCoord μ (g e b) + ...` (4 terms) ⭐
   - Block 3 (ΓΓ): `sumIdx fun ρ => ...`

2. **What `payload_cancel_all` actually proves**:
   - Pattern: `dCoord(g) * Γtot` (NOT `Γtot * dCoord(g)`)
   - This means the lemma might be stated with flipped factors

3. **Required fix**:
   - Either: Adjust f₁-f₄ to match Block 2's exact syntax
   - Or: Use `mul_comm` to flip terms before applying `payload_cancel_all`
   - Or: Target the second sumIdx specifically (not the first)

---

## Specific Request to JP

Per your guidance:
> "If anything still blocks after you try this verbatim, paste the exact post-rw [h_payload_split]; rw [hP0]; simp goal (from InfoView) and I'll tailor a one‑line reshaper that matches your local add‑chain."

**We need**:

1. **How to target Block 2 (the second sumIdx) specifically**, not Block 1
2. **How to handle the `payload_cancel_all` factor order mismatch** (`dCoord(g) * Γtot` vs `Γtot * dCoord(g)`)
3. **Whether to use `mul_comm` before applying the lemma**, or adjust the f₁-f₄ definitions

### Alternative Approach

If JP's surgical extraction assumes a different goal structure, we may need to revisit **how steps 1-4 expand the terms**. Should we be using different expansion lemmas that produce the payload in the expected form?

---

## Build Context

- **Baseline errors**: 24
- **Current errors**: 25 (new error from JP's code)
- **File compiles**: ❌ (with errors)
- **Dependencies**: All ✅ PROVEN (expand_P_ab, expand_Ca, expand_Cb_for_C_terms_b, payload_cancel_all, etc.)

---

## Next Steps

**Option A**: Wait for JP's micro-collector tailored to our specific goal structure
**Option B**: Manually adjust f₁-f₄ and add `mul_comm` rewrites (but risky without JP's guidance)
**Option C**: Re-examine expansion lemmas to see if they can produce different goal structure

**Recommendation**: Send this diagnostic to JP and await his one-line reshaper or updated drop-in code.

---

**Prepared by**: Claude Code (Lean 4 Assistant)
**Date**: October 30, 2025
**Build log**: `build_jp_dropin_solution_oct30.txt`
**Code location**: Riemann.lean:9150-9214
**Priority**: **HIGH** - Blocking Four-Block assembly completion
