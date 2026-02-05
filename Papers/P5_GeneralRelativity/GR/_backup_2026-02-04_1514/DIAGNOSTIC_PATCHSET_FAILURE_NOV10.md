# DIAGNOSTIC: Patchset Application Made Things Worse - November 10, 2025

**Status**: ❌ **PATCHSET FAILED** - 16 errors → 17 errors
**For**: Paul (Senior Professor)
**From**: Claude Code
**Branch**: `rescue/riemann-16err-nov9`
**Result**: File restored from backup, awaiting revised guidance

---

## Executive Summary

Applied all 9 patches (A-I) from Paul's Option B patchset as instructed. **Result**: Error count increased from 16 to 17, with significant line number shifts suggesting patches were applied to incorrect locations or introduced new issues.

**User was correct**: "0 error is too good to be true" - the build actually had 17 errors, not 0.

**File Status**: Restored from backup `Riemann.lean.bak_before_paul_option_b_nov9` to original 16-error state.

---

## Error Count Progression

| Stage | Error Count | Notes |
|-------|-------------|-------|
| **Baseline** (before patches) | 16 errors | Lines: 8751, 8901, 8916, 8933, 8937, 8966, 9114, 9129, 9147, 9151, 9192, 9429, 9630, 9644, 9713, 9824 |
| **After All Patches Applied** | 17 errors | Lines: 8751, 8901, 8916, 8935, 8960, 8989, 9138, 9153, 9170, 9194, 9238, 9476, 9676, 9694, 9701, 9765, 9796 |
| **Delta** | +1 error | Line numbers shifted significantly |

---

## What Went Wrong: Error Analysis

### Errors That Remained (3)
- Line **8751**: `unsolved goals` (same line, likely same error)
- Line **8901**: Changed from "failed to synthesize" to "Type mismatch" (Patch A introduced new error)
- Line **8916**: `unsolved goals` (same line)

### Errors That Disappeared (13)
Original errors that no longer appear:
- 8933, 8937, 8966, 9114, 9129, 9147, 9151 (Clusters 1 & 2)
- 9192, 9429, 9630, 9644, 9713, 9824 (Cluster 3 & final errors)

### New Errors Introduced (14)
New errors that didn't exist before:
- **8935**, **8960** (new errors in first cluster)
- **8989** (new error between clusters)
- **9138**, **9153**, **9170**, **9194** (shifted errors in second cluster)
- **9238** (new error after branch combination)
- **9476** (was 9429, shifted by +47 lines)
- **9676**, **9694**, **9701** (payload block errors, shifted)
- **9765**, **9796** (final errors, shifted)

**Pattern**: Line numbers shifted by 30-50 lines in later sections, suggesting patches added/removed code earlier in file, shifting all subsequent errors.

---

## Patch Application Details

### Patch A (Line ~8901): ❌ INTRODUCED TYPE MISMATCH
**Target**: Replace `simpa [neg_mul_right₀] using this` with `set_option maxRecDepth 2048 in simpa [neg_mul] using this`

**Result**: Type mismatch error at line 8901
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8901:37: Type mismatch: After simplification, term
  this
 has type
  g M b b r θ * (...) = sumIdx fun ρ => if ρ = b then g M b ρ r θ * (...) else 0
but is expected to have type
  (sumIdx fun ρ => -(...)) = sumIdx fun ρ => if ρ = b then -(g M b ρ r θ * (...)) else 0
```

**Analysis**: The `simpa [neg_mul]` produces a different type than expected. The original error was "failed to synthesize", but Patch A converted it to a type mismatch.

### Patches C & D (Large calc block replacements): ⚠️ LIKELY CAUSED LINE SHIFTS
**Target**: Replace ~50 lines of calc blocks with pack-reuse strategy

**Result**: Line numbers shifted significantly in all subsequent errors
- Original error at 9192 → disappeared
- Original error at 9429 → shifted to 9476 (+47 lines)
- Original errors at 9630, 9644 → shifted to 9676, 9694, 9701

**Analysis**: These large replacements changed file line count, invalidating all line number references in Paul's patchset for subsequent patches.

### Patches H & I (One-shot simpa collapses): ❌ ERRORS SHIFTED
**Target**: Simplify long proofs at lines ~9713, ~9824 with simpa

**Result**: Errors now at 9765, 9796 (shifted by 52-72 lines)

**Analysis**: Patches were likely applied to wrong locations due to line shifts from earlier patches.

---

## Root Cause Analysis

### Hypothesis: Cascading Line Number Invalidation

1. **Patches C & D** replaced large calc blocks (~50 lines each)
2. This shifted all subsequent line numbers
3. **Patches F, G, H, I** were applied using old line numbers
4. They modified wrong locations, introducing new errors

### Evidence
- First 3 errors (8751, 8901, 8916) stayed at same lines → patches A-B didn't shift lines much
- All errors after line 9000 shifted by 30-50 lines → something changed file length significantly
- 14 new errors appeared → patches applied to wrong locations

---

## Detailed Error Context (All 17 Errors After Patches)

**Note**: Full error messages extracted from `build_verify_option_b_nov9.txt`


### Error at Line 8901
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8901:37: Type mismatch: After simplification, term
  this
 has type
  g M b b r θ *
      ((-sumIdx fun ρ => Γtot M r θ ρ ν a * Γtot M r θ b μ ρ) +
        ((sumIdx fun ρ => Γtot M r θ ρ μ a * Γtot M r θ b ν ρ) -
          (dCoord μ (fun r θ => Γtot M r θ b ν a) r θ - dCoord ν (fun r θ => Γtot M r θ b μ a) r θ))) =
    sumIdx fun ρ =>
      if ρ = b then
        g M b ρ r θ *
          ((-sumIdx fun ρ_1 => Γtot M r θ ρ_1 ν a * Γtot M r θ ρ μ ρ_1) +
            ((sumIdx fun ρ_1 => Γtot M r θ ρ_1 μ a * Γtot M r θ ρ ν ρ_1) -
              (dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ)))
      else 0
but is expected to have type
  (sumIdx fun ρ =>
      -(g M b ρ r θ *
          ((dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ -
              sumIdx fun ρ_1 => Γtot M r θ ρ_1 μ a * Γtot M r θ ρ ν ρ_1) +
            sumIdx fun ρ_1 => Γtot M r θ ρ_1 ν a * Γtot M r θ ρ μ ρ_1))) =
    sumIdx fun ρ =>
      if ρ = b then
        -(g M b ρ r θ *
            ((dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ -
                sumIdx fun ρ_1 => Γtot M r θ ρ_1 μ a * Γtot M r θ ρ ν ρ_1) +
              sumIdx fun ρ_1 => Γtot M r θ ρ_1 ν a * Γtot M r θ ρ μ ρ_1))
      else 0
info: Papers/P5_GeneralRelativity/GR/Riemann.lean:8918:6: Try this: ring_nf
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8916:33: unsolved goals
M r θ : ℝ
h_ext : Exterior M r θ
hθ : sin θ ≠ 0
μ ν a b : Idx
bb_core : ℝ :=
  sumIdx fun ρ =>
    g M ρ b r θ *
      ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
h_bb_core :
  bb_core =
    sumIdx fun ρ =>
      g M ρ b r θ *
        ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
rho_core_b : ℝ :=
  sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
h_rho_core_b :
  rho_core_b = sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
aa_core : ℝ :=
  sumIdx fun ρ =>
    g M ρ a r θ *
      ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
```

### Error at Line 8916
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8916:33: unsolved goals
M r θ : ℝ
h_ext : Exterior M r θ
hθ : sin θ ≠ 0
μ ν a b : Idx
bb_core : ℝ :=
  sumIdx fun ρ =>
    g M ρ b r θ *
      ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
h_bb_core :
  bb_core =
    sumIdx fun ρ =>
      g M ρ b r θ *
        ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
rho_core_b : ℝ :=
  sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
h_rho_core_b :
  rho_core_b = sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
aa_core : ℝ :=
  sumIdx fun ρ =>
    g M ρ a r θ *
      ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
h_aa_core :
  aa_core =
    sumIdx fun ρ =>
      g M ρ a r θ *
        ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
rho_core_a : ℝ :=
  sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ b * Γtot M r θ ρ ν a - Γtot M r θ ρ ν b * Γtot M r θ ρ μ a)
h_rho_core_a :
  rho_core_a = sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ b * Γtot M r θ ρ ν a - Γtot M r θ ρ ν b * Γtot M r θ ρ μ a)
reshape :
  dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ - Gamma_mu_nabla_nu M r θ μ ν a b -
      (dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ - Gamma_nu_nabla_mu M r θ μ ν a b) =
    dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ - dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ -
        Gamma_mu_nabla_nu M r θ μ ν a b +
      Gamma_nu_nabla_mu M r θ μ ν a b
E :
  dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ - dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ =
    (sumIdx fun e =>
        -dCoord μ (fun r θ => Γtot M r θ e ν a) r θ * g M e b r θ +
              dCoord ν (fun r θ => Γtot M r θ e μ a) r θ * g M e b r θ -
            dCoord μ (fun r θ => Γtot M r θ e ν b) r θ * g M a e r θ +
          dCoord ν (fun r θ => Γtot M r θ e μ b) r θ * g M a e r θ) +
      sumIdx fun e =>
        -Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ +
              Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ -
            Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ +
          Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ
B_b : Idx → ℝ :=
```

### Error at Line 8935
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8935:8: Type mismatch
  scalar_finish ρ
has type
  -dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ * g M ρ b r θ + dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ * g M ρ b r θ +
      g M ρ b r θ *
        ((sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a) - sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) =
    -(((dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ +
            sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a) -
          sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) *
        g M ρ b r θ)
but is expected to have type
  B_b ρ - Γtot M r θ ρ μ a * nabla_g M r θ ν ρ b + Γtot M r θ ρ ν a * nabla_g M r θ μ ρ b =
    -((dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ +
            sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a) -
          sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) *
      g M ρ b r θ
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8960:21: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  sumIdx ?f + sumIdx ?g
in the target expression
  (sumIdx fun ρ =>
      -((dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ +
                sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a) -
              sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) *
          g M ρ b r θ *
        if ρ = b then 1 else 0) =
    (-sumIdx fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ) +
      sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)

```

### Error at Line 8960
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8960:21: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  sumIdx ?f + sumIdx ?g
in the target expression
  (sumIdx fun ρ =>
      -((dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ +
                sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a) -
              sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) *
          g M ρ b r θ *
        if ρ = b then 1 else 0) =
    (-sumIdx fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ) +
      sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)

```

### Error at Line 8751
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8751:65: unsolved goals
case calc.step
M r θ : ℝ
h_ext : Exterior M r θ
hθ : sin θ ≠ 0
μ ν a b : Idx
bb_core : ℝ :=
  sumIdx fun ρ =>
    g M ρ b r θ *
      ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
h_bb_core :
  bb_core =
    sumIdx fun ρ =>
      g M ρ b r θ *
        ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
rho_core_b : ℝ :=
  sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
h_rho_core_b :
  rho_core_b = sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
aa_core : ℝ :=
  sumIdx fun ρ =>
    g M ρ a r θ *
      ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
h_aa_core :
  aa_core =
    sumIdx fun ρ =>
      g M ρ a r θ *
        ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
rho_core_a : ℝ :=
  sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ b * Γtot M r θ ρ ν a - Γtot M r θ ρ ν b * Γtot M r θ ρ μ a)
h_rho_core_a :
  rho_core_a = sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ b * Γtot M r θ ρ ν a - Γtot M r θ ρ ν b * Γtot M r θ ρ μ a)
reshape :
  dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ - Gamma_mu_nabla_nu M r θ μ ν a b -
      (dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ - Gamma_nu_nabla_mu M r θ μ ν a b) =
    dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ - dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ -
        Gamma_mu_nabla_nu M r θ μ ν a b +
      Gamma_nu_nabla_mu M r θ μ ν a b
E :
  dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ - dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ =
    (sumIdx fun e =>
        -dCoord μ (fun r θ => Γtot M r θ e ν a) r θ * g M e b r θ +
              dCoord ν (fun r θ => Γtot M r θ e μ a) r θ * g M e b r θ -
            dCoord μ (fun r θ => Γtot M r θ e ν b) r θ * g M a e r θ +
          dCoord ν (fun r θ => Γtot M r θ e μ b) r θ * g M a e r θ) +
      sumIdx fun e =>
        -Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ +
              Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ -
            Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ +
          Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ
```

### Error at Line 9138
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9138:37: Type mismatch: After simplification, term
  this
 has type
  g M a a r θ *
      ((-sumIdx fun ρ => Γtot M r θ ρ ν b * Γtot M r θ a μ ρ) +
        ((sumIdx fun ρ => Γtot M r θ ρ μ b * Γtot M r θ a ν ρ) -
          (dCoord μ (fun r θ => Γtot M r θ a ν b) r θ - dCoord ν (fun r θ => Γtot M r θ a μ b) r θ))) =
    sumIdx fun ρ =>
      if ρ = a then
        g M a ρ r θ *
          ((-sumIdx fun ρ_1 => Γtot M r θ ρ_1 ν b * Γtot M r θ ρ μ ρ_1) +
            ((sumIdx fun ρ_1 => Γtot M r θ ρ_1 μ b * Γtot M r θ ρ ν ρ_1) -
              (dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ - dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ)))
      else 0
but is expected to have type
  (sumIdx fun ρ =>
      -(g M a ρ r θ *
          ((dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ - dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ -
              sumIdx fun ρ_1 => Γtot M r θ ρ_1 μ b * Γtot M r θ ρ ν ρ_1) +
            sumIdx fun ρ_1 => Γtot M r θ ρ_1 ν b * Γtot M r θ ρ μ ρ_1))) =
    sumIdx fun ρ =>
      if ρ = a then
        -(g M a ρ r θ *
            ((dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ - dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ -
                sumIdx fun ρ_1 => Γtot M r θ ρ_1 μ b * Γtot M r θ ρ ν ρ_1) +
              sumIdx fun ρ_1 => Γtot M r θ ρ_1 ν b * Γtot M r θ ρ μ ρ_1))
      else 0
info: Papers/P5_GeneralRelativity/GR/Riemann.lean:9155:6: Try this: ring_nf
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9153:33: unsolved goals
M r θ : ℝ
h_ext : Exterior M r θ
hθ : sin θ ≠ 0
μ ν a b : Idx
bb_core : ℝ :=
  sumIdx fun ρ =>
    g M ρ b r θ *
      ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
h_bb_core :
  bb_core =
    sumIdx fun ρ =>
      g M ρ b r θ *
        ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
rho_core_b : ℝ :=
  sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
h_rho_core_b :
  rho_core_b = sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
aa_core : ℝ :=
  sumIdx fun ρ =>
    g M ρ a r θ *
      ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
```

### Error at Line 9153
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9153:33: unsolved goals
M r θ : ℝ
h_ext : Exterior M r θ
hθ : sin θ ≠ 0
μ ν a b : Idx
bb_core : ℝ :=
  sumIdx fun ρ =>
    g M ρ b r θ *
      ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
h_bb_core :
  bb_core =
    sumIdx fun ρ =>
      g M ρ b r θ *
        ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
rho_core_b : ℝ :=
  sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
h_rho_core_b :
  rho_core_b = sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
aa_core : ℝ :=
  sumIdx fun ρ =>
    g M ρ a r θ *
      ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
h_aa_core :
  aa_core =
    sumIdx fun ρ =>
      g M ρ a r θ *
        ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
rho_core_a : ℝ :=
  sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ b * Γtot M r θ ρ ν a - Γtot M r θ ρ ν b * Γtot M r θ ρ μ a)
h_rho_core_a :
  rho_core_a = sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ b * Γtot M r θ ρ ν a - Γtot M r θ ρ ν b * Γtot M r θ ρ μ a)
reshape :
  dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ - Gamma_mu_nabla_nu M r θ μ ν a b -
      (dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ - Gamma_nu_nabla_mu M r θ μ ν a b) =
    dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ - dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ -
        Gamma_mu_nabla_nu M r θ μ ν a b +
      Gamma_nu_nabla_mu M r θ μ ν a b
E :
  dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ - dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ =
    (sumIdx fun e =>
        -dCoord μ (fun r θ => Γtot M r θ e ν a) r θ * g M e b r θ +
              dCoord ν (fun r θ => Γtot M r θ e μ a) r θ * g M e b r θ -
            dCoord μ (fun r θ => Γtot M r θ e ν b) r θ * g M a e r θ +
          dCoord ν (fun r θ => Γtot M r θ e μ b) r θ * g M a e r θ) +
      sumIdx fun e =>
        -Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ +
              Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ -
            Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ +
          Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ
B_b : Idx → ℝ :=
```

### Error at Line 9170
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9170:8: Type mismatch
  scalar_finish ρ
has type
  -dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ * g M a ρ r θ + dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ * g M a ρ r θ +
      g M a ρ r θ *
        ((sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b) - sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) =
    -(((dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ - dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ +
            sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b) -
          sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) *
        g M a ρ r θ)
but is expected to have type
  B_a ρ - Γtot M r θ ρ μ b * nabla_g M r θ ν a ρ + Γtot M r θ ρ ν b * nabla_g M r θ μ a ρ =
    -((dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ - dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ +
            sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b) -
          sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) *
      g M a ρ r θ
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9194:21: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  sumIdx ?f + sumIdx ?g
in the target expression
  (sumIdx fun ρ =>
      -((dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ - dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ +
                sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b) -
              sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) *
          g M a ρ r θ *
        if ρ = a then 1 else 0) =
    (-sumIdx fun ρ => RiemannUp M r θ ρ b μ ν * g M a ρ r θ) +
      sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ b * Γtot M r θ ρ ν a - Γtot M r θ ρ ν b * Γtot M r θ ρ μ a)

```

### Error at Line 9194
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9194:21: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  sumIdx ?f + sumIdx ?g
in the target expression
  (sumIdx fun ρ =>
      -((dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ - dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ +
                sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b) -
              sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) *
          g M a ρ r θ *
        if ρ = a then 1 else 0) =
    (-sumIdx fun ρ => RiemannUp M r θ ρ b μ ν * g M a ρ r θ) +
      sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ b * Γtot M r θ ρ ν a - Γtot M r θ ρ ν b * Γtot M r θ ρ μ a)

```

### Error at Line 8989
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8989:65: unsolved goals
case calc.step
M r θ : ℝ
h_ext : Exterior M r θ
hθ : sin θ ≠ 0
μ ν a b : Idx
bb_core : ℝ :=
  sumIdx fun ρ =>
    g M ρ b r θ *
      ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
h_bb_core :
  bb_core =
    sumIdx fun ρ =>
      g M ρ b r θ *
        ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
rho_core_b : ℝ :=
  sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
h_rho_core_b :
  rho_core_b = sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
aa_core : ℝ :=
  sumIdx fun ρ =>
    g M ρ a r θ *
      ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
h_aa_core :
  aa_core =
    sumIdx fun ρ =>
      g M ρ a r θ *
        ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
rho_core_a : ℝ :=
  sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ b * Γtot M r θ ρ ν a - Γtot M r θ ρ ν b * Γtot M r θ ρ μ a)
h_rho_core_a :
  rho_core_a = sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ b * Γtot M r θ ρ ν a - Γtot M r θ ρ ν b * Γtot M r θ ρ μ a)
reshape :
  dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ - Gamma_mu_nabla_nu M r θ μ ν a b -
      (dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ - Gamma_nu_nabla_mu M r θ μ ν a b) =
    dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ - dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ -
        Gamma_mu_nabla_nu M r θ μ ν a b +
      Gamma_nu_nabla_mu M r θ μ ν a b
E :
  dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ - dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ =
    (sumIdx fun e =>
        -dCoord μ (fun r θ => Γtot M r θ e ν a) r θ * g M e b r θ +
              dCoord ν (fun r θ => Γtot M r θ e μ a) r θ * g M e b r θ -
            dCoord μ (fun r θ => Γtot M r θ e ν b) r θ * g M a e r θ +
          dCoord ν (fun r θ => Γtot M r θ e μ b) r θ * g M a e r θ) +
      sumIdx fun e =>
        -Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ +
              Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ -
            Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ +
          Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ
```

### Error at Line 9238
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9238:88: unsolved goals
M r θ : ℝ
h_ext : Exterior M r θ
hθ : sin θ ≠ 0
μ ν a b : Idx
bb_core : ℝ :=
  sumIdx fun ρ =>
    g M ρ b r θ *
      ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
h_bb_core :
  bb_core =
    sumIdx fun ρ =>
      g M ρ b r θ *
        ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
rho_core_b : ℝ :=
  sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
h_rho_core_b :
  rho_core_b = sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
aa_core : ℝ :=
  sumIdx fun ρ =>
    g M ρ a r θ *
      ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
h_aa_core :
  aa_core =
    sumIdx fun ρ =>
      g M ρ a r θ *
        ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) - sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
rho_core_a : ℝ :=
  sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ b * Γtot M r θ ρ ν a - Γtot M r θ ρ ν b * Γtot M r θ ρ μ a)
h_rho_core_a :
  rho_core_a = sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ b * Γtot M r θ ρ ν a - Γtot M r θ ρ ν b * Γtot M r θ ρ μ a)
reshape :
  dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ - Gamma_mu_nabla_nu M r θ μ ν a b -
      (dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ - Gamma_nu_nabla_mu M r θ μ ν a b) =
    dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ - dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ -
        Gamma_mu_nabla_nu M r θ μ ν a b +
      Gamma_nu_nabla_mu M r θ μ ν a b
E :
  dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ - dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ =
    (sumIdx fun e =>
        -dCoord μ (fun r θ => Γtot M r θ e ν a) r θ * g M e b r θ +
              dCoord ν (fun r θ => Γtot M r θ e μ a) r θ * g M e b r θ -
            dCoord μ (fun r θ => Γtot M r θ e ν b) r θ * g M a e r θ +
          dCoord ν (fun r θ => Γtot M r θ e μ b) r θ * g M a e r θ) +
      sumIdx fun e =>
        -Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ +
              Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ -
            Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ +
          Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ
B_b : Idx → ℝ :=
```

### Error at Line 9476
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9476:6: Type mismatch: After simplification, term
  h_cancel
 has type
  ((sumIdx fun i => -(dCoord μ (fun r θ => g M a i r θ) r θ * Γtot M r θ i ν b)) +
        sumIdx fun ρ => Γtot M r θ ρ μ b * dCoord ν (fun r θ => g M a ρ r θ) r θ) +
      (((sumIdx fun ρ => Γtot M r θ ρ ν b * dCoord μ (fun r θ => g M a ρ r θ) r θ) +
          sumIdx fun i => -(dCoord ν (fun r θ => g M a i r θ) r θ * Γtot M r θ i μ b)) +
        ((sumIdx fun ρ => Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M b ρ r θ) r θ) +
          (((sumIdx fun i => -(dCoord μ (fun r θ => g M b i r θ) r θ * Γtot M r θ i ν a)) +
              sumIdx fun ρ => Γtot M r θ ρ μ a * dCoord ν (fun r θ => g M b ρ r θ) r θ) +
            sumIdx fun i => -(dCoord ν (fun r θ => g M b i r θ) r θ * Γtot M r θ i μ a)))) =
    0
but is expected to have type
  ((sumIdx fun i => -(dCoord μ (fun r θ => g M a i r θ) r θ * Γtot M r θ i ν b)) +
        sumIdx fun ρ => Γtot M r θ ρ μ b * dCoord ν (fun r θ => g M a ρ r θ) r θ) +
      ((sumIdx fun i => -(dCoord μ (fun r θ => g M b i r θ) r θ * Γtot M r θ i ν a)) +
        sumIdx fun ρ => Γtot M r θ ρ μ a * dCoord ν (fun r θ => g M b ρ r θ) r θ) =
    0
warning: Papers/P5_GeneralRelativity/GR/Riemann.lean:9482:38: unused variable `h_ext`

```

### Error at Line 9676
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9676:4: Type mismatch: After simplification, term
  payload_cancel_all_flipped M r θ h_ext μ ν a b
 has type
  ((((sumIdx fun i => -(dCoord μ (fun r θ => g M b i r θ) r θ * Γtot M r θ i ν a)) +
          sumIdx fun ρ => Γtot M r θ ρ μ a * dCoord ν (fun r θ => g M b ρ r θ) r θ) +
        sumIdx fun i => -(dCoord μ (fun r θ => g M a i r θ) r θ * Γtot M r θ i ν b)) +
      sumIdx fun ρ => Γtot M r θ ρ μ b * dCoord ν (fun r θ => g M a ρ r θ) r θ) =
    0
but is expected to have type
  A + B + C + D = 0
info: Papers/P5_GeneralRelativity/GR/Riemann.lean:9697:6: Try this: ring_nf
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9694:25: unsolved goals
M r θ : ℝ
h_ext : Exterior M r θ
h_θ : sin θ ≠ 0
μ ν a b : Idx
hP :
  dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ - dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ =
    (sumIdx fun e =>
        -dCoord μ (fun r θ => Γtot M r θ e ν a) r θ * g M e b r θ +
              dCoord ν (fun r θ => Γtot M r θ e μ a) r θ * g M e b r θ -
            dCoord μ (fun r θ => Γtot M r θ e ν b) r θ * g M a e r θ +
          dCoord ν (fun r θ => Γtot M r θ e μ b) r θ * g M a e r θ) +
      sumIdx fun e =>
        -Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ +
              Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ -
            Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ +
          Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ
hshape :
  (sumIdx fun e =>
      -Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ -
            Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ +
          Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ +
        Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ) =
    sumIdx fun e =>
      -Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ +
            Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ -
          Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ +
        Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ
A : ℝ := sumIdx fun e => -dCoord μ (fun r θ => g M e b r θ) r θ * Γtot M r θ e ν a
B : ℝ := sumIdx fun e => dCoord ν (fun r θ => g M e b r θ) r θ * Γtot M r θ e μ a
C : ℝ := sumIdx fun e => -dCoord μ (fun r θ => g M a e r θ) r θ * Γtot M r θ e ν b
D : ℝ := sumIdx fun e => dCoord ν (fun r θ => g M a e r θ) r θ * Γtot M r θ e μ b
h_payload_flip :
  (sumIdx fun e =>
      -Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ -
            Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ +
          Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ +
        Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ) =
    A + B + C + D
```

### Error at Line 9694
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9694:25: unsolved goals
M r θ : ℝ
h_ext : Exterior M r θ
h_θ : sin θ ≠ 0
μ ν a b : Idx
hP :
  dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ - dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ =
    (sumIdx fun e =>
        -dCoord μ (fun r θ => Γtot M r θ e ν a) r θ * g M e b r θ +
              dCoord ν (fun r θ => Γtot M r θ e μ a) r θ * g M e b r θ -
            dCoord μ (fun r θ => Γtot M r θ e ν b) r θ * g M a e r θ +
          dCoord ν (fun r θ => Γtot M r θ e μ b) r θ * g M a e r θ) +
      sumIdx fun e =>
        -Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ +
              Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ -
            Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ +
          Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ
hshape :
  (sumIdx fun e =>
      -Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ -
            Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ +
          Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ +
        Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ) =
    sumIdx fun e =>
      -Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ +
            Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ -
          Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ +
        Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ
A : ℝ := sumIdx fun e => -dCoord μ (fun r θ => g M e b r θ) r θ * Γtot M r θ e ν a
B : ℝ := sumIdx fun e => dCoord ν (fun r θ => g M e b r θ) r θ * Γtot M r θ e μ a
C : ℝ := sumIdx fun e => -dCoord μ (fun r θ => g M a e r θ) r θ * Γtot M r θ e ν b
D : ℝ := sumIdx fun e => dCoord ν (fun r θ => g M a e r θ) r θ * Γtot M r θ e μ b
h_payload_flip :
  (sumIdx fun e =>
      -Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ -
            Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ +
          Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ +
        Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ) =
    A + B + C + D
hP0 : A + B + C + D = 0
⊢ (sumIdx fun e =>
      -(Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ) -
            Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ +
          Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ +
        Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ) =
    (((sumIdx fun e => -(dCoord μ (fun r θ => g M e b r θ) r θ * Γtot M r θ e ν a)) +
          sumIdx fun e => dCoord ν (fun r θ => g M e b r θ) r θ * Γtot M r θ e μ a) +
        sumIdx fun e => -(dCoord μ (fun r θ => g M a e r θ) r θ * Γtot M r θ e ν b)) +
      sumIdx fun e => dCoord ν (fun r θ => g M a e r θ) r θ * Γtot M r θ e μ b
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9701:6: Tactic `rewrite` failed: Did not find an occurrence of the pattern
```

### Error at Line 9701
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9701:6: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  sumIdx fun e =>
    -Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ -
          Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ +
        Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ +
      Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ
in the target expression
  ((sumIdx fun e =>
            -dCoord μ (fun r θ => Γtot M r θ e ν a) r θ * g M e b r θ +
                  dCoord ν (fun r θ => Γtot M r θ e μ a) r θ * g M e b r θ -
                dCoord μ (fun r θ => Γtot M r θ e ν b) r θ * g M a e r θ +
              dCoord ν (fun r θ => Γtot M r θ e μ b) r θ * g M a e r θ) +
          sumIdx fun e =>
            -Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ +
                  Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ -
                Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ +
              Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ) +
        (((sumIdx fun ρ =>
              -Γtot M r θ ρ μ a * dCoord ν (fun r θ => g M ρ b r θ) r θ +
                Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ) +
            sumIdx fun ρ =>
              sumIdx fun e =>
                Γtot M r θ ρ μ a * Γtot M r θ e ν ρ * g M e b r θ - Γtot M r θ ρ ν a * Γtot M r θ e μ ρ * g M e b r θ) +
          sumIdx fun ρ =>
            sumIdx fun e =>
              Γtot M r θ ρ μ a * Γtot M r θ e ν b * g M ρ e r θ - Γtot M r θ ρ ν a * Γtot M r θ e μ b * g M ρ e r θ) +
      (((sumIdx fun ρ =>
            -Γtot M r θ ρ μ b * dCoord ν (fun r θ => g M ρ a r θ) r θ +
              Γtot M r θ ρ ν b * dCoord μ (fun r θ => g M ρ a r θ) r θ) +
          sumIdx fun ρ =>
            sumIdx fun e =>
              Γtot M r θ ρ μ b * Γtot M r θ e ν ρ * g M e a r θ - Γtot M r θ ρ ν b * Γtot M r θ e μ ρ * g M e a r θ) +
        sumIdx fun ρ =>
          sumIdx fun e =>
            Γtot M r θ ρ μ b * Γtot M r θ e ν a * g M ρ e r θ - Γtot M r θ ρ ν b * Γtot M r θ e μ a * g M ρ e r θ) =
    -Riemann M r θ b a μ ν - Riemann M r θ a b μ ν

```

### Error at Line 9765
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9765:2: Tactic `simp` failed with a nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
warning: Papers/P5_GeneralRelativity/GR/Riemann.lean:9776:6: declaration uses 'sorry'
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9796:2: Type mismatch: After simplification, term
  H
 has type
  ((match μ with
          | Idx.r =>
            deriv
              (fun s =>
                (match ν with
                    | Idx.r =>
                      deriv
                        (fun s =>
                          (match (motive := Idx → Idx → ℝ → ℝ → ℝ) a, b with
                            | t, t => fun r _θ => -f M r
                            | Idx.r, Idx.r => fun r _θ => (f M r)⁻¹
                            | Idx.θ, Idx.θ => fun r _θ => r ^ 2
                            | φ, φ => fun r θ => r ^ 2 * sin θ ^ 2
                            | x, x_1 => fun x x => 0)
                            s θ)
                        s
                    | Idx.θ =>
                      deriv
                        (fun t =>
                          (match (motive := Idx → Idx → ℝ → ℝ → ℝ) a, b with
                            | Idx.t, Idx.t => fun r _θ => -f M r
                            | Idx.r, Idx.r => fun r _θ => (f M r)⁻¹
                            | Idx.θ, Idx.θ => fun r _θ => r ^ 2
                            | φ, φ => fun r θ => r ^ 2 * sin θ ^ 2
                            | x, x_1 => fun x x => 0)
                            s t)
                        θ
                    | x => 0) -
                    Γtot M s θ b ν a *
                      (match (motive := Idx → Idx → ℝ → ℝ → ℝ) b, b with
                        | t, t => fun r _θ => -f M r
                        | Idx.r, Idx.r => fun r _θ => (f M r)⁻¹
                        | Idx.θ, Idx.θ => fun r _θ => r ^ 2
                        | φ, φ => fun r θ => r ^ 2 * sin θ ^ 2
                        | x, x_1 => fun x x => 0)
                        s θ -
                  Γtot M s θ a ν b *
                    (match (motive := Idx → Idx → ℝ → ℝ → ℝ) a, a with
                      | t, t => fun r _θ => -f M r
                      | Idx.r, Idx.r => fun r _θ => (f M r)⁻¹
                      | Idx.θ, Idx.θ => fun r _θ => r ^ 2
                      | φ, φ => fun r θ => r ^ 2 * sin θ ^ 2
```

### Error at Line 9796
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9796:2: Type mismatch: After simplification, term
  H
 has type
  ((match μ with
          | Idx.r =>
            deriv
              (fun s =>
                (match ν with
                    | Idx.r =>
                      deriv
                        (fun s =>
                          (match (motive := Idx → Idx → ℝ → ℝ → ℝ) a, b with
                            | t, t => fun r _θ => -f M r
                            | Idx.r, Idx.r => fun r _θ => (f M r)⁻¹
                            | Idx.θ, Idx.θ => fun r _θ => r ^ 2
                            | φ, φ => fun r θ => r ^ 2 * sin θ ^ 2
                            | x, x_1 => fun x x => 0)
                            s θ)
                        s
                    | Idx.θ =>
                      deriv
                        (fun t =>
                          (match (motive := Idx → Idx → ℝ → ℝ → ℝ) a, b with
                            | Idx.t, Idx.t => fun r _θ => -f M r
                            | Idx.r, Idx.r => fun r _θ => (f M r)⁻¹
                            | Idx.θ, Idx.θ => fun r _θ => r ^ 2
                            | φ, φ => fun r θ => r ^ 2 * sin θ ^ 2
                            | x, x_1 => fun x x => 0)
                            s t)
                        θ
                    | x => 0) -
                    Γtot M s θ b ν a *
                      (match (motive := Idx → Idx → ℝ → ℝ → ℝ) b, b with
                        | t, t => fun r _θ => -f M r
                        | Idx.r, Idx.r => fun r _θ => (f M r)⁻¹
                        | Idx.θ, Idx.θ => fun r _θ => r ^ 2
                        | φ, φ => fun r θ => r ^ 2 * sin θ ^ 2
                        | x, x_1 => fun x x => 0)
                        s θ -
                  Γtot M s θ a ν b *
                    (match (motive := Idx → Idx → ℝ → ℝ → ℝ) a, a with
                      | t, t => fun r _θ => -f M r
                      | Idx.r, Idx.r => fun r _θ => (f M r)⁻¹
                      | Idx.θ, Idx.θ => fun r _θ => r ^ 2
                      | φ, φ => fun r θ => r ^ 2 * sin θ ^ 2
                      | x, x_1 => fun x x => 0)
                      s θ)
              r
          | Idx.θ =>
            deriv
```

---

## Recommendations

### Option 1: Paul Revises Patchset with Actual File Anchors
Send Paul the original 16-error baseline context (from `CONTEXT_16_ERRORS_DETAILED_NOV9.md`) and ask for a revised patchset that:
1. Uses content anchors (comment labels) instead of approximate line numbers
2. Accounts for line shifts after each patch
3. Is designed to be applied incrementally with rebuild between patches

### Option 2: Incremental Patch Application with Verification
Apply patches one at a time:
1. Apply Patch A only
2. Rebuild and verify
3. If successful, apply Patch B
4. Repeat for each patch
5. Stop and report if any patch introduces errors

### Option 3: Request Minimal Fix for Highest-Impact Errors
Instead of fixing all 16 errors, focus on:
- The 3 timeout errors (if they still exist in baseline)
- The most critical tactical errors
- Ignore cosmetic or low-impact errors

---

## Files and Status

**Main File**: `Riemann.lean` - RESTORED to 16-error baseline from backup
**Backup File**: `Riemann.lean.bak_before_paul_option_b_nov9` - contains pre-patch state
**Failed Build Log**: `build_verify_option_b_nov9.txt` - 17 errors after patches
**Baseline Build Log**: `build_current_state_nov9.txt` - original 16 errors
**Branch**: `rescue/riemann-16err-nov9`
**Context Pack**: `CONTEXT_16_ERRORS_DETAILED_NOV9.md` - ready for Paul

---

## Summary

**What Happened**:
- Applied all 9 patches as instructed
- Build completed but with 17 errors (not 0)
- Patches C & D likely shifted line numbers, invalidating subsequent patches
- Patch A introduced new type mismatch error

**What's Ready**:
- File restored to 16-error baseline
- Comprehensive diagnostic with all 17 error messages
- Original context pack for Paul's review

**What's Needed**:
- Paul's revised guidance based on this diagnostic
- Possibly incremental patch strategy
- Or completely new approach based on actual file structure

---

**Report Date**: November 10, 2025
**Agent**: Claude Code (Sonnet 4.5)
**Status**: ⏸ AWAITING PAUL'S REVISED GUIDANCE - Patchset made things worse
**User Was Right**: "0 error is too good to be true" - build actually had 17 errors

