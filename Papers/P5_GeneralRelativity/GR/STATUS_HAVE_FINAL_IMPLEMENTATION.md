# Status: Have Final Implementation
**Date**: October 20, 2025
**Status**: In Progress - Debugging compilation errors

---

## WHAT WE DID

✅ **Implemented JP's have final proof body** at lines 4607-4776
- Added complete proof with explicit steps
- Used prod_rule_backwards_sum for step0
- Applied Cancel_r_expanded and Cancel_θ_expanded
- Used sumIdx_collect4 and pointwise RiemannUp recognition
- Structured as deterministic calc chain

---

## CURRENT COMPILATION ERRORS

**Build Command**:
```bash
lake build Papers.P5_GeneralRelativity.GR.Riemann
```

**Errors**:
1. Line 4776:35: "unexpected token 'have'; expected ':='"
2. Line 4606:79: "unsolved goals"
3. Line 4756:4: "'calc' expression has type..." (incomplete error message)
4. Line 4335:60: "unsolved goals" (in outer proof)

---

## ISSUES IDENTIFIED AND FIXED

### Fixed Issue 1: Indentation
**Problem**: `classical` wasn't indented properly
**Fix**: Added proper indentation at line 4607

### Fixed Issue 2: prod_rule_backwards_sum rearrangement
**Problem**: The lemma gives `A = dCoord - C`, not `dCoord = A + C`
**Solution**: Rewrote h_r_back and h_θ_back to use:
```lean
have h := prod_rule_backwards_sum M r θ h_ext h_θ a Idx.θ Idx.r b
calc dCoord ... = A + C := by simp [A, C]; linarith [h]
```

---

## REMAINING ISSUES

### Issue 1: step3 and step4 References
The calc uses `simp [step3]` and `simp [step4]` but these steps should be defined earlier in the proof. Need to verify they exist and are accessible.

### Issue 2: Type Mismatch in calc
The error "calc' expression has type" suggests the final calc expression doesn't match the expected type of `have final`.

---

## DEBUGGING STRATEGY

### Next Steps:
1. **Verify all intermediate steps exist**:
   - Check that step0, step1, step2, step3, step4 are all properly defined
   - Ensure they're in scope when referenced in calc

2. **Check calc type**:
   - The calc should prove exactly what `have final` declares
   - May need to adjust final step to match goal exactly

3. **Simplify for debugging**:
   - Replace complex `simp [step3]` with explicit step references
   - Use `exact step3` instead of `by simp [step3]`

---

## CODE LOCATION

**File**: `Papers/P5_GeneralRelativity/GR/Riemann.lean`

**Key sections**:
- Line 4598-4606: `have final` type signature
- Line 4607-4776: Proof body (JP's implementation)
- Line 4756-4776: Final calc chain
- Line 4778-4973: Commented old proof body
- Line 4975+: Continuation with hSigma, etc.

---

## RECOMMENDED FIX APPROACH

Based on the errors, I recommend:

**Option A: Explicit step references**
Replace:
```lean
_ = (sumIdx (fun ρ => f₁ ρ - f₂ ρ + f₃ ρ - f₄ ρ)) + (Extra_r - Extra_θ) := by simp [step3]
```

With:
```lean
_ = (sumIdx (fun ρ => f₁ ρ - f₂ ρ + f₃ ρ - f₄ ρ)) + (Extra_r - Extra_θ) := by
  rw [← step3]; rfl
```

**Option B: Verify step definitions**
Ensure step3 proves:
```lean
have step3 :
  (A - B) + (M_r - M_θ) = sumIdx (fun ρ => f₁ ρ - f₂ ρ + f₃ ρ - f₄ ρ)
```

And step4 proves:
```lean
have step4 :
  sumIdx (fun ρ => f₁ ρ - f₂ ρ + f₃ ρ - f₄ ρ)
  = sumIdx (fun ρ => g M a ρ r θ * RiemannUp M r θ ρ b Idx.r Idx.θ)
```

---

## NEXT SESSION TODO

1. Get detailed error message for "calc' expression has type"
2. Verify step3 and step4 are properly defined and in scope
3. Test simpler calc structure with explicit `rw` instead of `simp`
4. If needed, break calc into explicit transitivity chain

---

**Prepared by**: Claude Code
**Date**: October 20, 2025
**Status**: Debugging in progress - close to completion
