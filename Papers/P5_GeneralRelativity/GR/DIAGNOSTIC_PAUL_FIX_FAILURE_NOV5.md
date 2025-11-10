# DIAGNOSTIC: Why Paul's Forward-Direction Fix Fails

**Date**: November 5, 2025
**Context**: Step 9 (δ-insertion error)
**Status**: 🔴 **Paul's fix doesn't work - error persists with different message**

---

## Discovery

The user correctly identified that the error count remaining at 18 (instead of decreasing to 17) indicates **the error was not fixed**.

### Evidence

**Baseline (Step 8)**: Error at line 9283
- Error: `unsolved goals`
- Location: `branches_sum` calc proof, line `rw [← hb, ← ha]`

**Current (Step 9 - Paul's fix)**: Error at line 9219
- Error: `Tactic 'assumption' failed`
- Location: `branches_sum` calc proof (new version), line `simpa [hb, ha]`
- **Shift**: -64 lines (9283 → 9219)

**Conclusion**: The error just moved and changed its error message. Paul's fix didn't eliminate the problem.

---

## Why Paul's Approach Fails

### The Core Issue

Paul's guidance was:
1. Group the LHS with `ring` to match `hb` and `ha` shapes
2. Apply `simpa [hb, ha]` to collapse both branches forward
3. Normalize with `ring`

But `simpa [hb, ha]` is failing with "Tactic `assumption` failed", which means Lean can't close the proof even after simplification.

### Root Cause: Type Mismatch

Looking at the types:

**`hb` proves** (lines 8746-8751):
```lean
(sumIdx B_b)
- sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
+ sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
=
- sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
```

**But `hb`'s calc chain produces** (lines 8934-8948):
```lean
_   = - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
    + rho_core_b
```

**The problem**: The calc proves `LHS = RHS + rho_core_b`, but the type signature claims `LHS = RHS`. This only typechecks if there's another calc step that proves `RHS + rho_core_b = RHS`, which would require `rho_core_b = 0`.

### Checking if rho_core_b = 0

Looking for where `rho_core_b` is defined and whether it equals zero...

**Key Question**: Does `diag_cancel` prove that `rho_core_b + rho_core_a = 0` **individually**, or only their sum?

If `rho_core_b = 0` and `rho_core_a = 0` individually, then `hb` and `ha` would typecheck correctly.

But if only `rho_core_b + rho_core_a = 0` (their sum is zero, but individually they're non-zero), then:
- `hb` and `ha` have incorrect type signatures (should include `+ rho_core_b/a`)
- Paul's forward approach can't work because `hb` and `ha` don't actually prove what their types claim

---

## Next Steps

Need to investigate:

1. **What does `diag_cancel` prove?** Does it prove individual terms are zero, or only their sum?

2. **Why does `hb` typecheck?** If the calc proves `LHS = RHS + rho_core_b` but the type says `LHS = RHS`, there must be an implicit step eliminating `rho_core_b`. Is Lean inferring that `rho_core_b = 0`?

3. **Can we use `hb` and `ha` as-is?** If they prove the collapsed form (without rho_core terms), then the baseline approach (`rw [← hb, ← ha]`) was trying to use them backward incorrectly. But Paul's forward approach also fails.

4. **Alternative**: Maybe the issue is that we need to explicitly provide the intermediate forms, not try to extract them from `hb`/`ha`.

---

## Action Required

**Option A**: Investigate why `hb` typechecks despite apparent type mismatch
- Read the end of `hb`'s calc (after line 8948) to see if there are more steps
- Check if Lean is automatically applying `rho_core_b = 0`

**Option B**: Check `diag_cancel` definition to understand what it proves
- If `diag_cancel` proves `rho_core_b = 0` and `rho_core_a = 0` individually, we can use them
- If it only proves their sum is zero, we need a different approach

**Option C**: Abandon using `hb`/`ha` and inline the proof
- The baseline `branches_sum` was trying to compose `hb` and `ha`, but maybe they're not meant to be composed
- Instead, manually prove `branches_sum` with its own calc chain

---

## Recommendation

I recommend **Option A + B** first (investigate the type system behavior), then **Option C** if needed.

**Reason**: Understanding why the current structure fails will inform the correct fix, rather than guessing at another approach that might also fail.

---

**Status**: Awaiting investigation into `hb` typecheck behavior and `diag_cancel` definition.
