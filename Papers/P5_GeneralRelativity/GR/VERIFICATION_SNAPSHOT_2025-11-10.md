# Verification Snapshot - November 10, 2025 (21:51 UTC)

**Build Log**: `build_test_fix_9755_nov10.txt` (created 21:15 UTC)
**Error Index**: `Riemann_error_index_2025-11-10.txt`
**Total Errors**: 14
**Distribution**: 7 unsolved goals | 4 type mismatches | 3 rewrite failures

---

## Error Index (Machine-Readable)

| Line | Col | Type |
|------|-----|------|
| 8751 | 65  | unsolved goals |
| 8933 | 33  | unsolved goals |
| 8950 | 8   | Type mismatch |
| 8954 | 12  | Tactic `rewrite` failed |
| 8983 | 65  | unsolved goals |
| 9169 | 33  | unsolved goals |
| 9187 | 8   | Type mismatch |
| 9191 | 12  | Tactic `rewrite` failed |
| 9232 | 88  | unsolved goals |
| 9469 | 15  | Type mismatch |
| 9670 | 4   | Type mismatch |
| 9684 | 6   | Tactic `rewrite` failed |
| 9755 | 13  | `simp` made no progress |
| 9865 | 57  | unsolved goals |

---

## Line Map (Semantic Anchors)

### Bucket 1: Unsolved Goals (7 errors)

**8751:65 - `hb` signature (nested calc)**
- **Context**: Line 8751 marks end of `have hb :` signature in b-branch δ-insertion proof
- **Anchor**: `- sumIdx (fun ρ => RiemannUp...) := by` (outer declaration)
- **Error**: `case calc.step` - indicates nested calc proof is incomplete
- **Note**: Actual incomplete step is inside `hb` proof body (lines 8752-8966)

**8933:33 - `scalar_finish` signature (nested calc)**
- **Context**: Line 8933 marks end of `have scalar_finish :` signature inside `hb` proof
- **Anchor**: `... * g M ρ b r θ ) := by` (line 8933)
- **Error**: `case calc.step` - nested calc issue
- **Body**: Lines 8921-8935 (proof is `intro ρ; ring`)

**8983:65 - Incomplete proof**
- **Context**: End of calc chain or sumIdx_congr block
- **Anchor**: TBD (needs source inspection)

**9169:33 - `scalar_finish` in a-branch (nested calc)**
- **Context**: Similar to line 8933 but in a-branch δ-insertion proof
- **Anchor**: Inside `ha` proof body
- **Error**: `case calc.step`

**9232:88 - Unsolved goal**
- **Context**: δ-cancellation attempt
- **Anchor**: TBD (repair plan says "Type mismatch" but build log says "unsolved goals")
- **Note**: Discrepancy between repair plan and actual error type

**9755:13 - LHS0 proof (dCoord unfolding)**
- **Context**: Line 9755 inside `have LHS0 :` proof
- **Anchor**: Commutator LHS simplification using metric compatibility
- **Error**: "`simp` made no progress" after attempted fix
- **Original error**: Line 9753 showed "unsolved goals", shifted after modification

**9865:57 - Incomplete proof**
- **Context**: Near end of file
- **Anchor**: TBD

---

### Bucket 2: Type Mismatches (4 errors)

**8950:8 - δ-cancellation shape mismatch**
- **Context**: b-branch δ-insertion, attempting to cancel delta
- **Anchor**: After payload normalization step
- **Cause**: Payload shape doesn't match `insert_delta_right_diag` conclusion
- **Fix**: Need pointwise normalization before applying δ-lemma

**9187:8 - δ-cancellation shape mismatch**
- **Context**: a-branch δ-insertion, similar to 8950
- **Anchor**: After payload normalization step
- **Fix**: Need pointwise normalization + commutation for left-metric case

**9469:15 - Type mismatch**
- **Context**: Later block
- **Anchor**: TBD

**9670:4 - Type mismatch**
- **Context**: Later block
- **Anchor**: TBD

---

### Bucket 3: Rewrite Failures (3 errors)

**8954:12 - "Did not find occurrence"**
- **Context**: Attempting `rw` under `sumIdx` binder
- **Cause**: `rw` can't reach inside `fun ρ =>`
- **Fix**: Wrap with `sumIdx_congr` or use `refine sumIdx_congr (fun ρ => ?_)`

**9191:12 - "Did not find occurrence"**
- **Context**: Similar to 8954 but in a-branch
- **Fix**: Same as above

**9684:6 - "Did not find occurrence"**
- **Context**: Later block
- **Fix**: Same pattern

---

## Current File State

**Sections Known Working** (verified by inspection):
- ✅ Section 1 (b-branch δ, lines ~8893-8918): Paul's equality-chaining pattern
- ✅ Section 2 (a-branch δ, lines ~9125-9154): Paul's equality-chaining pattern

**Modified Lines** (experimental fixes):
- Lines 9753-9755: Changed from `simp [h_r, h_θ', dCoord]; ring` to `simp [h_θ', h_r, dCoord, deriv_const]`
- Status: ⏳ Testing in progress

---

## Notes on Line Number Drift

**Discrepancy Found**: Repair plan (`PAUL_MECHANICAL_TRIAGE_14_ERRORS_NOV10.md`) shows different error type distribution than actual build log:

| Source | Unsolved Goals | Type Mismatches | Rewrite Failures |
|--------|----------------|-----------------|------------------|
| Repair Plan | 6 | 5 | 3 |
| Actual Build | 7 | 4 | 3 |

**Cause**: Line 9232 classified as "Type mismatch" in repair plan but shows "unsolved goals" in build log.

**Impact**: Affects Phase 1 target count (unsolved goals to fix).

---

## Next Steps (Per JP's Marching Orders)

### Phase 1: Nested-Calc "Unsolved Goals" (3 targets)
Fix lines **8751**, **8933**, **9169** (all show `case calc.step`)

**Strategy**:
1. Trace from outer signature to actual incomplete calc step
2. Complete missing step with explicit `calc` chain
3. Use deterministic tactics: `exact`, `congrArg`, `mul_assoc`, `neg_mul`
4. Avoid `simp`/`simpa` under binders

### Phase 2 & 3: Type Mismatches and Rewrite Failures
Apply Paul's templates systematically after Phase 1 completion.

---

**Report Generated**: 2025-11-10 21:52 UTC
**Build Log**: `build_test_fix_9755_nov10.txt`
**Agent**: Claude Code (Sonnet 4.5)
**Status**: ✅ Verification snapshot complete, ready for Phase 1

