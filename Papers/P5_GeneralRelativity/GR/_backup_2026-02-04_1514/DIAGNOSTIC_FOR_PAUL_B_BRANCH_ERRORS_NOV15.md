# Diagnostic Report: b-Branch Cascade Errors - November 15, 2024

**Status**: 15 errors remaining, 3 in b-branch section
**For**: Paul
**From**: Claude Code

---

## Executive Summary

Applied your ring fix (line 8898) and δ-collapse fix (lines 8900-8924) successfully. Error count reduced 19→15. However, **3 cascade errors remain** in the b-branch calc block that you expected to resolve:

1. **Line 8939**: `scalar_finish` proof has unsolved goals (intro ρ; ring doesn't close)
2. **Line 8956**: Type mismatch in calc block when applying `sumIdx_congr scalar_finish`
3. **Line 8960**: Rewrite pattern not found for `h_insert_delta_for_b`

**Key Finding**: `scalar_pack4` referenced at line 8877 **does not exist** as a lemma.

---

## Detailed Error Analysis

### Error 1: Line 8939 (scalar_finish unsolved goals)

**Code** (lines 8927-8941):
```lean
have scalar_finish :
  ∀ ρ,
    ( -(dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ) * g M ρ b r θ
      +  (dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ) * g M ρ b r θ )
    +  ( g M ρ b r θ *
          ( sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
           -sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) ) )
    =
      - ( ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
           - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
           + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
           - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) )
          * g M ρ b r θ ) := by
  intro ρ
  ring
```

**Error message**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8939:33: unsolved goals
[context shows: bb_core, h_bb_core, rho_core_b definitions]
```

**Analysis**: The `ring` tactic fails to close the goal. This could mean:
- The algebraic equality is false (sign error in the statement)
- Or the expression contains non-ring terms

### Error 2: Line 8956 (calc block type mismatch)

**Code** (lines 8954-8956):
```lean
simp only [nabla_g, RiemannUp, sub_eq_add_neg]
have H := sumIdx_congr scalar_finish
exact H  -- ❌ Error here
```

**Error message**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8956:8: Type mismatch
  H
has type
  (sumIdx fun i =>
      -dCoord μ (fun r θ => Γtot M r θ i ν a) r θ * g M i b r θ +
          dCoord ν (fun r θ => Γtot M r θ i μ a) r θ * g M i b r θ +
        g M i b r θ *
          ((sumIdx fun e => Γtot M r θ i μ e * Γtot M r θ e ν a) -
            sumIdx fun e => Γtot M r θ i ν e * Γtot M r θ e μ a)) =
    sumIdx fun i =>
      -(((dCoord μ (fun r θ => Γtot M r θ i ν a) r θ - dCoord ν (fun r θ => Γtot M r θ i μ a) r θ +
              sumIdx fun e => Γtot M r θ i μ e * Γtot M r θ e ν a) -
            sumIdx fun e => Γtot M r θ i ν e * Γtot M r θ e μ a) *
          g M i b r θ)
but is expected to have type
  ((sumIdx B_b + ...
```

**Analysis**: `H := sumIdx_congr scalar_finish` produces an equality between two `sumIdx` expressions, but we need an equality that starts with `(sumIdx B_b + ...`. The intermediate form doesn't match the calc block's expected type.

### Error 3: Line 8960 (rewrite pattern not found)

**Code** (lines 8959-8960):
```lean
simp only [h_rho_core_b]
rw [h_insert_delta_for_b, ← sumIdx_add_distrib]  -- ❌ Error here
```

**Error message**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8960:12: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  sumIdx fun ρ => -(G ρ * g M ρ b r θ)
in the target expression
  (sumIdx fun ρ =>
      -((dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ +
              sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a) -
            sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) *
        g M ρ b r θ) =
    (-sumIdx fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ) +
      sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
```

**Analysis**: The rewrite `h_insert_delta_for_b` expects pattern `sumIdx fun ρ => -(G ρ * g M ρ b r θ)`, but the actual target has a different structure: `sumIdx fun ρ => -((...)*g M ρ b r θ)` where the payload is expanded inline instead of being `G ρ`.

---

## Related Issue: scalar_pack4 Missing

**Line 8877** (in `scalar_finish_bb` proof):
```lean
simpa [mul_comm] using scalar_pack4 A B C D gbb
```

**Problem**:
1. This uses `simpa` with `mul_comm` (AC lemma violation!)
2. `scalar_pack4` **does not exist** in the codebase (grep confirmed)

This suggests the file may have drifted from your expected state, or `scalar_pack4` needs to be created.

---

## Questions for Paul

1. **Is `scalar_pack4` supposed to exist?** If so, what's its signature and where should it be defined?

2. **For the `scalar_finish` proof (lines 8927-8941)**: The `ring` tactic fails to close the goal. Is there a sign error in the RHS?

3. **Your original guidance** said these 3 errors would cascade-resolve after the δ-collapse fix. Why might they still be failing?

4. **Pattern C guidance**: You mentioned fixing the calc block by chaining equalities with `.trans` instead of fragile `exact H` and `rw`. Can you provide the exact replacement pattern?

---

## Current File State

**Lines 8885-8924**: Your δ-collapse fix ✅ (deterministic, no AC lemmas)
**Lines 8855-8879**: `scalar_finish_bb` proof ❌ (uses `simpa [mul_comm]` + missing `scalar_pack4`)
**Lines 8927-8941**: `scalar_finish` proof ❌ (ring tactic fails)
**Lines 8944-8971**: Calc block ❌ (cascade errors from scalar_finish)

---

## Next Steps Options

**Option A**: Create the missing `scalar_pack4` lemma and fix `scalar_finish_bb`
**Option B**: Fix the `scalar_finish` statement (possible sign error) and retry `ring`
**Option C**: Apply Pattern C to bypass `scalar_finish` entirely with direct `.trans` chaining

**Recommendation**: Option B or C, since Paul's guidance focused on making the proofs deterministic without AC lemmas.

---

**Report Time**: November 15, 2024
**Current Error Count**: 15 total (3 in b-branch, 12 elsewhere)
**Action Needed**: Paul's guidance on how to proceed with these 3 cascade errors

