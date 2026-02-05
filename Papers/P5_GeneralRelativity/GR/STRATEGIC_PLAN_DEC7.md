# Strategic Plan: Fixing Riemann.lean Errors
**Date**: December 7, 2024
**Current Status**: 18 unique error locations (20 total errors)

## Problem Analysis

### What Went Wrong
Our previous approach has been treating symptoms rather than root causes:
- We fixed individual tactical errors without addressing underlying issues
- Some "fixes" just moved errors to different locations
- The error count hasn't decreased meaningfully despite multiple fixes

### Root Cause Identification
The **hscal identity with `sorry` at line 9088** appears to be a critical blocker:
```lean
have hscal :
  (- dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
    + dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
    + (sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
      - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a)))
  = - (RiemannUp M r θ ρ a μ ν)
```

This identity is fundamental to the proof structure and its incompleteness cascades through the rest of the proof.

## Strategic Approach

### Phase 1: Fix Root Causes (Priority 1)
1. **Complete the hscal identity proof**
   - This is Paul's original algebraic identity
   - Ring/abel tactics can't handle functional operations (dCoord, sumIdx)
   - Need manual algebraic manipulation
   - Strategy: Unfold RiemannUp definition and show equality term-by-term

2. **Verify the sumIdx_delta proof at line 8943**
   - Our conv_rhs approach might be incorrect
   - Check if the proof actually establishes the required equality

### Phase 2: Systematic Error Resolution (Priority 2)
Work from **top to bottom** to avoid dependency issues:

1. **Line 8797**: Unsolved goals (likely due to hscal sorry)
2. **Line 8943**: Verify our delta collapse is correct
3. **Line 9002**: Unknown issue (investigate)
4. **Line 9040**: Related to Hpoint proof
5. Continue sequentially...

### Phase 3: Cleanup (Priority 3)
1. **Review all our "fixes"**
   - Determine which actually helped vs. just moved problems
   - Consider reverting changes that didn't reduce error count

2. **Clean rebuild**
   - After core fixes, do a clean lake build
   - Some errors might be cache artifacts

## Implementation Steps

### Step 1: Tackle hscal Identity
```lean
-- Current (with sorry):
sorry

-- Target proof structure:
unfold RiemannUp
simp only [dCoord, sumIdx]
-- Show LHS = RHS by algebraic manipulation
-- May need helper lemmas for:
--   - Distributing negation
--   - Rearranging sumIdx terms
--   - Commuting dCoord with other operations
```

### Step 2: Create Helper Lemmas
If standard tactics fail, create specific lemmas:
- `dCoord_neg`: Negation distributes over dCoord
- `sumIdx_difference`: Difference of sumIdx equals sumIdx of differences
- `RiemannUp_expanded`: Expanded form of RiemannUp

### Step 3: Test Each Fix Incrementally
- Fix one error
- Build immediately
- Verify error count decreases (not just moves)
- Only proceed if successful

## Success Metrics
- **Primary**: Total error count < 10
- **Secondary**: No sorry placeholders
- **Tertiary**: Clean build without warnings

## Risk Mitigation
- **Backup current state** before major changes
- **Document each fix** with before/after error counts
- **Be ready to revert** if fixes make things worse

## Timeline Estimate
1. Phase 1 (Root Causes): 2-3 hours
2. Phase 2 (Systematic Resolution): 3-4 hours
3. Phase 3 (Cleanup): 1 hour

Total: 6-8 hours of focused work

## Key Insight
We need to stop patching symptoms and address the fundamental algebraic identity that's blocking the proof flow. Once hscal is properly proven, many downstream errors should resolve automatically.