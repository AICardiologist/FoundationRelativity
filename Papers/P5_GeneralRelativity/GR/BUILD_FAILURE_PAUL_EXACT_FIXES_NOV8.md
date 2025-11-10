# BUILD FAILURE: Paul's Exact Surgical Fixes - November 8, 2025

**Status**: 🔴 **FAILED - Error count increased from 19 to 24**

## Summary

I applied Paul's exact surgical fixes verbatim:
1. **Fix 1**: Simplified `sumIdx_mul_ite_pick` to alias `sumIdx_delta_right` (lines 1858-1861)
2. **Fix 2**: Replaced `hb_plus` proof with 3-step calc implementation (lines 8796-8872)

## Build Results

- **Before**: 19 errors (baseline from error_messages_nov8.txt)
- **After**: 24 errors (from build_hb_plus_partial_nov8.txt)
- **Net change**: +5 errors ❌

## Error Analysis

### Original Error Lines (19 errors):
```
8848, 8855, 9005, 9020, 9037, 9041, 9072, 9123, 
9271, 9286, 9304, 9308, 9348, 9353, 9594, 9795, 
9809, 9878, 9989
```

### Current Error Lines (24 errors):
```
1862, 8275, 8836, 8853, 8872, 8878, 8886, 9036, 
9053, 9073, 9079, 9110, 9161, 9309, 9326, 9346, 
9352, 9397, 9401, 9641, 9842, 9856, 9927, 10036
```

### NEW Errors Introduced:

#### 1. Line 1862 - sumIdx_mul_ite_pick lemma failure
Error: Tactic 'unfold' failed to unfold 'Papers.P5_GeneralRelativity.Schwarzschild.sumIdx_expand'

Code applied (lines 1858-1861):
```lean
@[simp] private lemma sumIdx_mul_ite_pick (F : Idx → ℝ) (b : Idx) :
  sumIdx (fun ρ => F ρ * (if ρ = b then (1 : ℝ) else 0)) = F b :=
by simpa using sumIdx_delta_right F b
```

Problem: The simpa using sumIdx_delta_right F b tactic is trying to unfold definitions that don't exist or aren't accessible.

#### 2. Lines 8836, 8872 - hb_plus proof failures
Line 8836: Type mismatch in h_rewrite helper
Line 8872: Type mismatch in final calc step

#### 3. Lines 8878, 8886 - Cascading errors in hb proof
These are in the ORIGINAL hb proof (not modified), likely cascading from hb_plus failure.

## Root Cause

1. sumIdx_delta_right not working as expected with simpa
2. Type mismatches in hb_plus calc chain - goal states don't match expectations
3. Cascading failures affecting downstream proofs

## Next Steps

BLOCKED - Need Paul's guidance:
1. Should sumIdx_mul_ite_pick use 'rw' instead of 'simpa'?
2. What is the actual type mismatch at line 8836?
3. Should I revert these changes?

File: /Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean
Build: /Users/quantmann/FoundationRelativity/build_hb_plus_partial_nov8.txt
Date: November 8, 2025 22:45
