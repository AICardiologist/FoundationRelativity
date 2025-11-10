# DIAGNOSTIC: 8 Remaining Errors - November 9, 2025

**Status**: Extracted error details per JP's request
**File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`
**Build Log**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/build_rollback_complete_nov9.txt`

---

## Error Summary (8 errors total)

| Line | Error Type | Category | Context |
|------|------------|----------|---------|
| **8819** | `simp` timeout at `whnf` (200k heartbeats) | TIMEOUT | h_pack simp in hb_plus |
| **8852** | timeout at `«tactic execution»` (200k heartbeats) | TIMEOUT | h_delta in hb_plus |
| **9102** | timeout at `«tactic execution»` (200k heartbeats) | TIMEOUT | hb proof |
| **9650** | Type mismatch | TYPE MISMATCH | h_cancel application |
| **9851** | Type mismatch | TYPE MISMATCH | Unknown context |
| **9865** | `rewrite` failed - pattern not found | REWRITE PATTERN NOT FOUND | Unknown context |
| **9936** | `assumption` failed | TACTIC FAILURE | Unknown context |
| **10045** | `assumption` failed | TACTIC FAILURE | Unknown context |

---

## Detailed Error Messages

### Error 1: Line 8819 (h_pack simp timeout)

**Error**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8819:6: Tactic `simp` failed with a nested error:
(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

**Code context** (lines 8810-8820):
```lean
have h_pack :
    (sumIdx B_b)
    - sumIdx (fun ρ => Γtot M r θ ρ μ a * nabla_g M r θ ν ρ b)
    + sumIdx (fun ρ => Γtot M r θ ρ ν a * nabla_g M r θ μ ρ b)
  =
    sumIdx (fun ρ =>
      B_b ρ
      - Γtot M r θ ρ μ a * nabla_g M r θ ν ρ b
      + Γtot M r θ ρ ν a * nabla_g M r θ μ ρ b) := by
  -- canonical packers for finite sums
  simp [sub_eq_add_neg, sumIdx_add_distrib, sumIdx_map_sub,
        add_comm, add_left_comm, add_assoc]
```

**JP's Recommended Fix**:
> "Add the tiny normalizers that you already defined to the local simp call only at this site:
> flatten₄₁, flatten₄₂ (your 'JP flatteners' for 4-term sums),
> group_add_sub (the (X+Y)-Z → (X-Z)+Y bridge)."

**Current lemma status**:
- `group_add_sub` exists at line 195 with `@[simp]`
- `flatten₄₁` exists at line 367 with `@[simp]`
- `flatten₄₂` exists at line 372 with `@[simp]`

All are already GLOBAL @[simp] lemmas. However, JP suggests adding them explicitly to the LOCAL simp call.

---

### Error 2: Line 8852 (h_delta timeout)

**Error**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8852:4: (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (200000) has been reached
```

**Code context** (lines 8852-8870):
```lean
have h_delta :
  sumIdx (fun ρ =>
    -(RiemannUp M r θ ρ a μ ν) * g M ρ b r θ
    + g M ρ ρ r θ *
        (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b
         - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b))
  =
  (- sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ))
  + rho_core_b := by
  have h_core :
    sumIdx (fun ρ =>
      g M ρ ρ r θ *
        (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b
         - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)) = rho_core_b := by
    simpa [rho_core_b]
  simpa [sumIdx_add_distrib, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
         h_core]
```

**Likely cause**: Cascade from h_pack timeout at line 8819, or excessive simp in h_core/final simpa.

---

### Error 3: Line 9102 (hb proof timeout)

**Error**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9102:2: (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (200000) has been reached
```

**Context**: This is in the `hb` proof (which uses `hb_plus` result).

**JP's Recommended Fix**:
> "hb normally reuses the output of hb_plus and then contracts one more index. The typical failure here is either:
> - A premature δ‑evaluation (which we learned not to do), or
> - A misplaced negation when moving from - Σ (RiemannUp · g) to the contracted form.
>
> Fix pattern, without changing architecture:
> 1. Invoke Riemann_contract_first immediately when you see sumIdx (fun ρ => g M a ρ r θ * …).
> 2. Keep negation on the scalar before contraction. If you see -(E ρ) * g_{ρb} and Lean tries to move the - through multiplication in the wrong direction (causing HasDistribNeg recursion), rewrite once with your local lemma flip_neg_prod (already defined) before contraction."

**Need to examine**: Code around line 9102 to see if Riemann_contract_first or flip_neg_prod are needed.

---

### Error 4: Line 9650 (Type mismatch in h_cancel)

**Error**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9650:15: Type mismatch
  h_cancel
has type
  ((((sumIdx fun ρ =>
            -Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ +
              Γtot M r θ ρ μ a * dCoord ν (fun r θ => g M ρ b r θ) r θ) +
          sumIdx fun ρ =>
            -Γtot M r θ ρ μ a * dCoord ν (fun r θ => g M ρ b r θ) r θ +
              Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ) +
        sumIdx fun ρ =>
          -Γtot M r θ ρ ν b * dCoord μ (fun r θ => g M a ρ r θ) r θ +
            Γtot M r θ ρ μ b * dCoord ν (fun r θ => g M a ρ r θ) r θ) +
      sumIdx fun ρ =>
        -Γtot M r θ ρ μ b * dCoord ν (fun r θ => g M a ρ r θ) r θ +
          Γtot M r θ ρ ν b * dCoord μ (fun r θ => g M a ρ r θ) r θ) =
    0
```

**JP's Recommended Fix**:
> "Replace any congrArg (fun x => x + H x) … with a subterm rewrite rw [sumIdx_add_distrib] targeted at the sum, then simp [flatten₄₁, flatten₄₂, group_add_sub]."

**Note**: This shows a 4-sum addition structure that needs flattening. The `h_cancel` lemma has a specific shape but the goal expects something else.

---

### Error 5: Line 9851 (Type mismatch)

**Error**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9851:4: Type mismatch
```

**Need to examine**: Context around line 9851 to see what type mismatch is occurring.

---

### Error 6: Line 9865 (Rewrite pattern not found)

**Error**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9865:6: Tactic `rewrite` failed: Did not find an occurrence of the pattern
```

**JP's Recommended Fix**:
> "a rewrite attempted to replace a 4‑term sumIdx expression after product‑rule expansion; Lean didn't find the pattern because the target grouped as ((∑ …) + (∑ …)) + ((∑ …) + (∑ …)).
>
> Fix: normalize to your flatteners before rewrite: simp [flatten₄₁, flatten₄₂, group_sub_add] and only then rw [the_lemma]. If the lemma is directional, use .symm explicitly to match."

**Need to examine**: What rewrite is being attempted and what pattern it's looking for.

---

### Error 7: Line 9936 (Assumption failed)

**Error**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9936:4: Tactic `assumption` failed
```

**Need to examine**: What assumption is expected in context.

---

### Error 8: Line 10045 (Assumption failed)

**Error**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:10045:4: Tactic `assumption` failed
```

**Need to examine**: What assumption is expected in context.

---

## JP's General Guidance for Errors 4-8 (algebraic_identity region)

### Root Causes:

1. **congrArg misuse over sumIdx + context**:
   - "congrArg (fun x => x + H x) (sumIdx_add_distrib …) produces a type mismatch"
   - Fix: "Use rw [sumIdx_add_distrib] at the exact redex (via conv_lhs / conv_rhs if necessary)"

2. **Rewrite misses due to unnormalized target**:
   - "Lean didn't find the pattern because the target grouped as ((∑ …) + (∑ …)) + ((∑ …) + (∑ …))"
   - Fix: "simp [flatten₄₁, flatten₄₂, group_sub_add] and only then rw [the_lemma]"

3. **Exploding goals from dCoord expansion**:
   - "Do not expand the match μ branches. Use your _of_diff infrastructure"
   - Fix: "First apply dCoord_sub_sub_regroup μ X Y Z r θ … to push dCoord across X - Y - Z"
   - Then: "apply dCoord_add_of_diff / dCoord_mul_of_diff once per layer, discharging side conditions with discharge_diff"

4. **HasDistribNeg recursion**:
   - "If you still see recursion depth complaints near a packaged scalar times a sum"
   - Fix: "rewrite -(A * g) with flip_neg_prod, package with scalar_pack4 / fold_diag_kernel₂, then call ring_nf once"

---

## Available Infrastructure

### Flatten/Group Normalizers
- `group_add_sub` (line 195) - `@[simp]` - `(X + Y) - Z = (X - Z) + Y`
- `flatten₄₁` (line 367) - `@[simp]` - Flattens 4-term sums (form 1)
- `flatten₄₂` (line 372) - `@[simp]` - Flattens 4-term sums (form 2)

**Status**: All exist as GLOBAL @[simp] lemmas. JP suggests adding them EXPLICITLY to local simp calls where needed.

### dCoord Infrastructure (to search for)
- `dCoord_sub_sub_regroup` - Pushes dCoord across X - Y - Z
- `dCoord_add_of_diff` - Handles dCoord over addition
- `dCoord_mul_of_diff` - Handles dCoord over multiplication
- `discharge_diff` - Discharges differentiability side conditions

### Negation Handling (to search for)
- `flip_neg_prod` - Rewrites `-(A * g)` to avoid HasDistribNeg recursion

### Contraction (to search for)
- `Riemann_contract_first` - Contracts index immediately

### Packaging (to search for)
- `scalar_pack4` - Packages scalar terms
- `fold_diag_kernel₂` - Folds diagonal kernel terms

---

## Questions for JP

1. **Flatten lemmas are already global @[simp]**: Should I still add them explicitly to the local simp calls, or does this indicate a different issue (e.g., the simp call is timing out before it gets to them)?

2. **Error cascading**: Are errors 8852 and 9102 likely cascading from the h_pack timeout at 8819? If so, fixing 8819 might resolve them automatically.

3. **Missing infrastructure**: Before applying fixes, should I verify that all the mentioned infrastructure lemmas exist?
   - `flip_neg_prod`
   - `Riemann_contract_first`
   - `dCoord_sub_sub_regroup`
   - `dCoord_add_of_diff`, `dCoord_mul_of_diff`
   - `discharge_diff`
   - `scalar_pack4`, `fold_diag_kernel₂`

4. **group_sub_add vs group_add_sub**: JP mentions `group_sub_add` for error 6, but I only found `group_add_sub`. Is this a typo, or should I search for/create `group_sub_add`?

5. **Errors 7-8 (assumption failures)**: Should I examine the code context first, or is there a common pattern for these?

---

## Next Steps (Awaiting JP Guidance)

### Option A: Apply fixes incrementally
1. Fix error 8819 (h_pack) first
2. Rebuild to see if errors 8852, 9102 cascade away
3. Then address remaining 4-8 individually

### Option B: Verify infrastructure first
1. Search for and verify all mentioned lemmas exist
2. Document any missing lemmas
3. Request verbatim implementations if needed
4. Then apply fixes

### Option C: Request code context examination
1. Extract code context for all 8 error lines
2. Provide detailed context to JP
3. Wait for specific micro-fixes

**Recommended**: Option C - extract full context and get JP's specific guidance before making changes.

---

## Files and Locations

### Main File
`/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`

**Error locations**:
- Lines 8810-8820: h_pack in hb_plus (ERROR at 8819)
- Lines 8852-8870: h_delta in hb_plus (ERROR at 8852)
- Line ~9102: hb proof (ERROR at 9102)
- Line ~9650: h_cancel application (ERROR at 9650)
- Line ~9851: Unknown type mismatch (ERROR at 9851)
- Line ~9865: Rewrite failure (ERROR at 9865)
- Line ~9936: Assumption failure (ERROR at 9936)
- Line ~10045: Assumption failure (ERROR at 10045)

### Build Logs
- **Current**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/build_rollback_complete_nov9.txt` (8 errors)

---

**Report Date**: November 9, 2025
**Agent**: Claude Code (Sonnet 4.5)
**Status**: Diagnostic complete - awaiting JP's specific micro-fixes
