# DIAGNOSTIC: Patch Anchor Mismatch - November 9, 2025

**Status**: ⚠️ **ANCHOR MISMATCH** - Patchset cannot be applied as specified
**For**: Paul/JP
**From**: Claude Code
**Issue**: Expected anchors and proof structure don't exist in current file

---

## Problem Summary

Paul's patchset expects:
1. Separate `h_pack`, `h_delta`, `hb` lemmas with specific anchor comments
2. Comments like "canonical packers for finite sums", "h_pack simp timeout", etc.
3. A specific proof architecture with distinct phases

**Actual file structure**:
- One large `have hb` proof starting at line 8746
- No separate `h_pack` or `h_delta` intermediate lemmas in the error region
- No anchor comments matching Paul's search phrases
- Errors occur INSIDE the `hb` proof, not in separate helper lemmas

---

## Anchor Search Results

### Expected Anchor 1: "canonical packers for finite sums" or "h_pack simp timeout"
**Result**: ❌ NOT FOUND

**Search command**:
```bash
grep -n "canonical packers\|h_pack simp timeout\|Pack→Congr→Sum" Riemann.lean
```
**Output**: No matches

### Expected Anchor 2: "Pack with the (already correct) −Σ ρ (RiemannUp⋅g)" or "h_delta simpa timeout"
**Result**: ❌ NOT FOUND

**Search command**:
```bash
grep -n "Pack with the.*already correct\|h_delta simpa timeout" Riemann.lean
```
**Output**: No matches

### Expected Anchor 3: "Assemble to get hb_partial with rho_core_b" or "hb calc timeout"
**Result**: ✅ PARTIAL MATCH

**Search command**:
```bash
grep -n "Assemble to get hb_partial\|hb calc timeout\|h_rho_core_b" Riemann.lean
```
**Output**:
```
8920:    /- 4) Assemble to get hb_partial with rho_core_b -/
```

---

## Actual File Structure at Error Lines

### Error Cluster 1 (Lines 8751-8937)

**Context around line 8751 (first error)**:
```lean
  have hb :
    (sumIdx B_b)
    - sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
    + sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
  =
    - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ) := by  // LINE 8751 ERROR
    classical

    -- 0) Open only the outer shells; keep sums atomic.
    simp only [nabla_g, RiemannUp, sub_eq_add_neg]

    /- 1) Cancel the Γ·∂g payload at Σ_ρ level.
          Keep it at Σ_ρ and use a tiny scalar `ring` under `sumIdx_congr`. -/
    have payload_cancel :
      sumIdx (fun ρ =>
        (-(Γtot M r θ ρ ν a) * dCoord μ (fun r θ => g M ρ b r θ) r θ
          + (Γtot M r θ ρ μ a) * dCoord ν (fun r θ => g M ρ b r θ) r θ)
        - ((Γtot M r θ ρ μ a) * dCoord ν (fun r θ => g M ρ b r θ) r θ
           - (Γtot M r θ ρ ν a) * dCoord μ (fun r θ => g M ρ b r θ) r θ)
      ) = 0 := by
      have h : ∀ ρ,
        ... = 0 := by
        intro ρ; ring
      simp only [h]
      exact sumIdx_zero

    /- 2) Reshape the ΓΓ·g quartet - b-branch splits into bb-core + ρρ-core. -/
    have ΓΓ_block :
        ( sumIdx (fun ρ => (Γtot M r θ ρ μ a) * sumIdx (fun e => Γtot M r θ e ν ρ * g M e b r θ))
        - sumIdx (fun ρ => (Γtot M r θ ρ ν a) * sumIdx (fun e => Γtot M r θ e μ ρ * g M e b r θ)) )
      + ( sumIdx (fun ρ => (Γtot M r θ ρ μ a) * sumIdx (fun e => Γtot M r θ e ν b * g M ρ e r θ))
        - sumIdx (fun ρ => (Γtot M r θ ρ ν a) * sumIdx (fun e => Γtot M r θ e μ b * g M ρ e r θ)) )
      =
        bb_core + rho_core_b := by
      classical
      // ... complex proof continues
```

**Key observations**:
1. This is ONE LARGE `have hb` proof, not separate lemmas
2. Errors occur at intermediate steps within the proof
3. There are internal `have payload_cancel` and `have ΓΓ_block` sub-lemmas
4. The proof structure is: hb → (payload_cancel, ΓΓ_block, other steps) → final goal

### Error Cluster 2 (Lines 8966-9151)

**This appears to be the SECOND copy of the same proof pattern** (likely for index `a` instead of `b`).

Similar structure:
- Another large `have ha` or similar proof
- Similar internal structure with payload cancellation and ΓΓ blocks
- Parallel errors at similar proof steps

### Error Cluster 3 (Lines 9192-9824)

**Context around line 9192**:
Line 9192 appears to be in a later section, possibly the final assembly or Ricci identity proof.

---

## What This Means for Patching

Paul's patchset assumes:

**Expected Structure**:
```lean
have h_pack := by  -- Fence 1 goes here
  simp [...]

have h_delta := by  -- Fence 2 goes here
  simpa [...]

have hb := by  -- Fence 3 goes here
  calc ...
```

**Actual Structure**:
```lean
have hb :
  <goal> := by
  classical
  simp only [nabla_g, RiemannUp, sub_eq_add_neg]  -- Line 8755

  have payload_cancel : ... := by
    <proof>

  have ΓΓ_block : ... := by  // Line 8777-8783
    classical
    // Complex nested proof with many steps
    // ERRORS occur in here

  // More steps...
```

---

## Impact on Patch Application

### Patch A (Bootstrap): ✅ CAN APPLY
The namespace line exists at line 15. This patch can be applied as written.

### Patch B (Fence 1 - h_pack): ❌ CANNOT APPLY
- No `have h_pack` exists in the error region
- The relevant code is INSIDE the `have hb` proof
- Need different anchoring strategy

### Patch C (Fence 2 - h_delta): ❌ CANNOT APPLY
- No `have h_delta` exists in the error region
- No matching anchor comments
- Need different anchoring strategy

### Patch D (Fence 3 - hb calc): ⚠️ PARTIAL MATCH
- `have hb` exists at line 8746
- But it's not a `calc` block - it's a complex multi-step proof
- Line 8920 has comment "/- 4) Assemble to get hb_partial with rho_core_b -/"
- Need to wrap the ENTIRE `have hb` proof, not just a calc section

### Patch E (normalize4): ⏸ LOCATION UNCLEAR
- Without proper anchors for Patches B-C, don't know where to apply normalize4
- Need Paul's guidance on actual error locations

---

## Recommended Next Steps

### Option 1: Paul Provides Revised Patchset
Based on actual file structure:
1. Bootstrap at line 15 (namespace Papers.P5_GeneralRelativity)
2. Fence the entire `have hb` proof at line 8746-8751
3. Fence internal `have ΓΓ_block` at line 8777-8783
4. Apply normalize4 at specific rw/simp sites Paul identifies

### Option 2: Extract Detailed Context Pack
Generate full context for all 16 errors so Paul can see the actual structure:

```bash
for L in 8751 8901 8916 8933 8937 8966 9114 9129 9147 9151 9192 9429 9630 9644 9713 9824; do
  echo "=== Riemann.lean:$L ===" >> CONTEXT_16_ERRORS_DETAILED_NOV9.md
  sed -n "/^error:.*Riemann.lean:$L:/,/^$/p" build_current_state_nov9.txt >> CONTEXT_16_ERRORS_DETAILED_NOV9.md
  nl -ba Riemann.lean | sed -n "$((L-15)),$((L+15))p" >> CONTEXT_16_ERRORS_DETAILED_NOV9.md
  echo "" >> CONTEXT_16_ERRORS_DETAILED_NOV9.md
done
```

### Option 3: Manual Application with Best Effort
I can attempt to:
1. Apply Patch A (bootstrap) ✅
2. Wrap the large `have hb` proof at line 8746 with a fence
3. Wrap internal `have ΓΓ_block` with a fence
4. Add normalize4 before visible rw/simp statements
5. Rebuild and report results

**Risk**: May not match Paul's intent, could introduce different issues.

---

## Questions for Paul

1. **Is this the correct file?**
   - Expected: File with h_pack/h_delta/hb separate lemmas
   - Actual: File with one large hb proof containing internal sub-lemmas
   - Could there be a different version or branch?

2. **Should I proceed with Option 3 (best effort)?**
   - Apply bootstrap
   - Fence the main `have hb` proof
   - Fence the internal `have ΓΓ_block`
   - Add normalize4 before rw statements
   - Accept risk of not matching exact intent

3. **Should I generate the detailed context pack first?**
   - Extract 30 lines around each of the 16 error lines
   - Include error messages from build log
   - Send complete picture to Paul for revised patchset

---

## Files and Status

**Main file**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`
**Branch**: `rescue/riemann-16err-nov9`
**Build log**: `build_current_state_nov9.txt` (16 errors)

**Namespace found**: Line 15 `namespace Papers.P5_GeneralRelativity`
**Main hb proof**: Line 8746-??? (extends past error cluster)
**Anchor match**: Line 8920 "/- 4) Assemble to get hb_partial with rho_core_b -/"

**Current state**: READY but BLOCKED - awaiting Paul's decision on how to proceed.

---

**Report Date**: November 9, 2025, ~22:30 UTC
**Agent**: Claude Code (Sonnet 4.5)
**Status**: ⏸ AWAITING PAUL'S REVISED GUIDANCE - File structure doesn't match patchset expectations
