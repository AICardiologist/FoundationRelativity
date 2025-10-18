# Git Hook Improvement Proposal - Post Phase 2B
## Date: October 18, 2025
## Current Work Stage: Phase 4 Preparation (Ricci Identity)

---

## Executive Summary

**Purpose**: Update the pre-commit hook to be more helpful and accurate for the current stage of work (Phases 4-6: completing remaining sorries).

**Current Status**: Hook is designed for earlier "activation mode" development phases, which are no longer relevant after Phase 2B completion.

**Proposal**: Streamline hook to focus on:
1. Build verification (keep - critical)
2. Sorry/axiom tracking (add - helpful for current work)
3. Remove obsolete activation mode checks (cleanup)

---

## Current Hook Analysis

### What the Hook Does

**File**: `.git/hooks/pre-commit` (97 lines)

**Main Functions**:
1. **Guard: sumIdx_expand locality** (lines 4-12)
   - Prevents global `[simp]` attribute on `sumIdx_expand`
   - **Status**: ✅ Still relevant

2. **Guard: RHS sections require gInv** (lines 14-22)
   - Checks Stage1_RHS sections have gInv defined
   - **Status**: ⚠️ Obsolete (Stage-1 work complete)

3. **Guard: LHS sections require activation** (lines 24-41)
   - Checks Stage1_LHS sections match ACTIVATION_STATUS
   - **Status**: ⚠️ Obsolete (Stage-1 work complete)

4. **Quality Gates: Riemann.lean** (lines 43-66)
   - Runs `./scripts/check.sh` with activation mode
   - Calls `check-activation.sh` and `check-baseline.sh`
   - **Status**: ✅ Partially relevant (baseline check good, activation check obsolete)

5. **Documentation Audits** (lines 68-84)
   - Audits Markdown link integrity
   - Audits documentation anchors
   - **Status**: ✅ Still relevant

6. **Riemann Signature Audits** (lines 86-97)
   - Audits Riemann tensor signatures
   - **Status**: ⚠️ May be obsolete (Stage-1 specific)

### Scripts Called

| Script | Purpose | Still Relevant? |
|--------|---------|-----------------|
| `check.sh` | Main check dispatcher | ✅ Yes |
| `check-activation.sh` | Verify activation mode consistency | ❌ No (Stage-1 only) |
| `check-baseline.sh` | Verify 0 build errors | ✅ YES (critical!) |
| `audit-doc-links.sh` | Check Markdown links | ✅ Yes |
| `audit-doc-anchors.sh` | Check Markdown anchors | ✅ Yes |
| `audit-riemann-signatures.sh` | Check Stage-1 signatures | ⚠️ Maybe (Stage-1 specific) |

---

## Problems with Current Hook

### Issue 1: Activation Mode Obsolescence

**Problem**: Hook checks for `ACTIVATION_STATUS` and Stage-1 sections that are no longer used.

**Evidence**:
```bash
# Hook extracts MODE from Riemann.lean
MODE="$(grep 'ACTIVATION_STATUS' Riemann.lean)"
# Then checks Stage1_LHS, Stage1_RHS sections
```

**Impact**:
- Adds complexity for no benefit
- Confusing for current work (Phases 4-6)
- May trigger false failures if code patterns match old guards

---

### Issue 2: No Sorry/Axiom Tracking

**Problem**: Hook doesn't track progress on sorries/axioms, which is the main focus now.

**What's Missing**:
- No warning if sorry count increases unexpectedly
- No celebration when sorry count decreases
- No check that axiom count stays at 0

**Current Workaround**: Manual checking with `grep`

---

### Issue 3: No Phase-Specific Guidance

**Problem**: Hook doesn't provide context about what phase of work we're in.

**What Would Help**:
- Show current sorry count and breakdown by category
- Highlight which sorries are blocking next milestones
- Provide encouragement for progress

---

## Proposed Improvements

### Option A: Minimal Update (Low Risk)

**Changes**:
1. Keep all current guards (defensive)
2. Add sorry/axiom tracking to output
3. Add phase context message

**Pros**: ✅ Safe, no breaking changes
**Cons**: ❌ Keeps obsolete code

---

### Option B: Moderate Modernization (Recommended)

**Changes**:
1. **Remove** activation mode checks (obsolete)
2. **Remove** Stage-1 section guards (obsolete)
3. **Keep** sumIdx_expand guard (still relevant)
4. **Keep** baseline build check (critical)
5. **Keep** documentation audits (still relevant)
6. **Add** sorry/axiom progress tracking
7. **Add** phase-specific guidance
8. **Simplify** check.sh to just call check-baseline.sh

**Pros**:
- ✅ Cleaner, more maintainable
- ✅ Focused on current work
- ✅ Helpful progress feedback

**Cons**:
- ⚠️ Removes safety guards (but they're for completed work)

---

### Option C: Comprehensive Overhaul (High Effort)

**Changes**: All of Option B plus:
- Rewrite hook in more structured format
- Add configuration file for phase-specific rules
- Add automatic sorry categorization
- Add git commit message suggestions

**Pros**: ✅ Very helpful, professional
**Cons**: ❌ High effort (4-6 hours)

---

## Recommended Approach: Option B

**Justification**:
- Stage-1 work is complete and frozen
- Activation modes are no longer used
- Current focus is completing sorries
- Build verification is the critical safety check
- Progress tracking would be motivating

---

## Proposed New Hook (Option B)

### Structure

```bash
#!/usr/bin/env bash
set -euo pipefail

# =================================================================
# Pre-commit Hook for FoundationRelativity (Post-Phase 2B)
# Phases 2A, 2B, 3 complete - Now working on Phases 4-6
# =================================================================

#-----------------------------------------------------------------
# GUARD 1: Keep sumIdx_expand local-only (never global [simp])
#-----------------------------------------------------------------
[... keep existing guard ...]

#-----------------------------------------------------------------
# GUARD 2: Build Verification (CRITICAL)
#-----------------------------------------------------------------
if git diff --cached --name-only | grep -qE '^Papers/P5_GeneralRelativity/GR/'; then
  echo "▶ Building Riemann.lean (incremental)..."

  # Run baseline check (0 errors required)
  ./scripts/check-baseline.sh || exit 1

  echo "▶ Analyzing progress..."

  # Show sorry/axiom counts
  ./scripts/check-progress.sh  # NEW SCRIPT
fi

#-----------------------------------------------------------------
# GUARD 3: Documentation Integrity
#-----------------------------------------------------------------
if git diff --cached --name-only | grep -qE '\.md$'; then
  echo "▶ Auditing documentation..."
  ./scripts/audit-doc-links.sh || exit 1
  ./scripts/audit-doc-anchors.sh || exit 1
fi

echo "✅ All checks passed!"
```

### New Script: check-progress.sh

```bash
#!/usr/bin/env bash
# Show current progress on sorries and axioms

RIEMANN_FILE="Papers/P5_GeneralRelativity/GR/Riemann.lean"

# Count sorries and axioms
SORRY_COUNT=$(grep -c "sorry" "$RIEMANN_FILE" || echo 0)
AXIOM_COUNT=$(grep -c "^axiom" "$RIEMANN_FILE" || echo 0)

# Category breakdown (approximate)
INFRA_SORRIES=$(grep -n "sorry" "$RIEMANN_FILE" | grep -E "416|424|6583|6608|6640|6642" | wc -l || echo 0)
REGROUP_SORRIES=$(grep -n "sorry" "$RIEMANN_FILE" | grep -E "3913|3979|6672|6685|6715|6741" | wc -l || echo 0)
RICCI_SORRIES=$(grep -n "sorry" "$RIEMANN_FILE" | grep -E "4020|4033" | wc -l || echo 0)
SYMMETRY_SORRIES=$(grep -n "sorry" "$RIEMANN_FILE" | grep -E "4041|4053|4059|4060" | wc -l || echo 0)

echo "📊 Progress Tracking:"
echo "   Axioms: $AXIOM_COUNT (target: 0) ✅"
echo "   Sorries: $SORRY_COUNT (target: 0)"
echo ""
echo "📋 Sorry Breakdown:"
echo "   Infrastructure: $INFRA_SORRIES (low priority)"
echo "   Regrouping: $REGROUP_SORRIES (Phase 4)"
echo "   Ricci Identity: $RICCI_SORRIES (Phase 4 - CRITICAL)"
echo "   Symmetry: $SYMMETRY_SORRIES (Phase 5)"
echo ""

# Show next milestone
if [ "$RICCI_SORRIES" -gt 0 ]; then
  echo "🎯 Next Milestone: Complete Ricci Identity (Phase 4)"
  echo "   Priority: Lines 3913, 3979, 4020, 4033"
elif [ "$SYMMETRY_SORRIES" -gt 0 ]; then
  echo "🎯 Next Milestone: Complete Symmetry (Phase 5)"
  echo "   Priority: Lines 4041, 4053"
elif [ "$SORRY_COUNT" -gt 0 ]; then
  echo "🎯 Next Milestone: Cleanup remaining infrastructure (Phase 6)"
else
  echo "🎉 ALL DONE! Zero sorries, zero axioms!"
fi
```

---

## Implementation Plan

### Step 1: Create Backup

```bash
cp .git/hooks/pre-commit .git/hooks/pre-commit.backup-pre-phase4
```

### Step 2: Create New Scripts

1. Create `scripts/check-progress.sh` (see above)
2. Simplify `scripts/check.sh` to remove activation mode

### Step 3: Update Hook

Replace `.git/hooks/pre-commit` with new version (see above)

### Step 4: Test

```bash
# Test with a small change
echo "# Test comment" >> Papers/P5_GeneralRelativity/GR/SORRY_AND_AXIOM_ANALYSIS_OCT18.md
git add Papers/P5_GeneralRelativity/GR/SORRY_AND_AXIOM_ANALYSIS_OCT18.md
git commit -m "test: verify updated hook"

# Should see:
# ▶ Building Riemann.lean (incremental)...
# ✅ Baseline OK (0 errors)
# 📊 Progress Tracking:
#    Axioms: 0 ✅
#    Sorries: 22
# 🎯 Next Milestone: Complete Ricci Identity (Phase 4)
# ✅ All checks passed!
```

### Step 5: Document

Update hook documentation in repository docs

---

## Alternative: Simpler Progress Script

If full categorization is too complex, a simpler version:

```bash
#!/usr/bin/env bash
# Simple progress tracker

SORRY_COUNT=$(grep -c "sorry" Papers/P5_GeneralRelativity/GR/Riemann.lean || echo 0)
AXIOM_COUNT=$(grep -c "^axiom" Papers/P5_GeneralRelativity/GR/Riemann.lean || echo 0)

echo "📊 Progress: $SORRY_COUNT sorries, $AXIOM_COUNT axioms"

if [ "$AXIOM_COUNT" -gt 0 ]; then
  echo "⚠️  Warning: Axioms detected! Target is 0."
fi

if [ "$SORRY_COUNT" -eq 0 ] && [ "$AXIOM_COUNT" -eq 0 ]; then
  echo "🎉 Perfect! All proven!"
elif [ "$SORRY_COUNT" -lt 20 ]; then
  echo "🎯 Almost there! Less than 20 sorries remaining."
fi
```

---

## Risk Assessment

### Option B Risks

**Risk 1**: Removing guards breaks something
- **Mitigation**: Stage-1 work is frozen, guards no longer apply
- **Probability**: Low
- **Impact**: Medium (would need to restore old hook)

**Risk 2**: New progress script has bugs
- **Mitigation**: Easy to fix, non-blocking
- **Probability**: Medium
- **Impact**: Low (just display issues)

**Risk 3**: Hook becomes too slow
- **Mitigation**: Progress script is just grep (fast)
- **Probability**: Very low
- **Impact**: Low (users can disable if needed)

---

## Benefits Analysis

### Option B Benefits

**Benefit 1**: Clearer understanding of progress
- Current sorry count visible on every commit
- Motivating to see count decrease
- Clear milestone guidance

**Benefit 2**: Simpler hook maintenance
- Less code to maintain
- Easier for future contributors to understand
- Focused on current work

**Benefit 3**: Better feedback loop
- Know immediately if axioms reintroduced
- Track sorry reduction progress
- Celebrate milestones

---

## Recommendation

**Implement Option B** with the following priorities:

1. **HIGH PRIORITY** (do now):
   - Create `check-progress.sh` (simple version)
   - Update hook to call it
   - Test thoroughly

2. **MEDIUM PRIORITY** (next session):
   - Remove obsolete activation mode checks
   - Simplify check.sh
   - Update documentation

3. **LOW PRIORITY** (future):
   - Add fancy categorization to progress script
   - Add commit message suggestions
   - Add celebration messages for milestones

---

## Current Hook vs Proposed Hook

### Current (97 lines, complex)

```
✅ Guards: sumIdx_expand
⚠️ Guards: Stage-1 RHS sections (obsolete)
⚠️ Guards: Stage-1 LHS sections (obsolete)
✅ Build: check-baseline.sh
⚠️ Build: check-activation.sh (obsolete)
✅ Docs: link/anchor audits
⚠️ Riemann: signature audits (maybe obsolete)

Output: "✅ All checks passed (mode=baseline)"
```

### Proposed (50 lines, focused)

```
✅ Guards: sumIdx_expand
✅ Build: check-baseline.sh
✅ Progress: check-progress.sh (NEW)
✅ Docs: link/anchor audits

Output:
"📊 Progress: 22 sorries, 0 axioms
 🎯 Next: Complete Ricci Identity (Phase 4)
 ✅ All checks passed!"
```

**Improvement**: Simpler, more helpful, focused on current work

---

## Files to Create/Modify

1. **NEW**: `scripts/check-progress.sh` (progress tracking)
2. **MODIFY**: `.git/hooks/pre-commit` (streamline)
3. **MODIFY**: `scripts/check.sh` (remove activation mode)
4. **BACKUP**: `.git/hooks/pre-commit.backup-pre-phase4`
5. **DOCUMENT**: This file (HOOK_IMPROVEMENT_PROPOSAL_OCT18.md)

---

## Testing Checklist

- [ ] Hook runs on GR file changes
- [ ] Hook skips on non-GR changes
- [ ] Build check catches errors
- [ ] Progress script shows correct counts
- [ ] Documentation audits still work
- [ ] Hook completes in reasonable time (<10s)
- [ ] Error messages are clear
- [ ] Success messages are helpful

---

## Future Enhancements

### When Phases 4-6 Complete

At zero sorries/axioms, update hook to:
- Display congratulations message
- Suggest running full test suite
- Recommend creating release tag
- Update README with achievement

### Potential Additions

- Track proof complexity metrics
- Warn if file size grows significantly
- Check for TODO/FIXME comments in new code
- Suggest related lemmas when adding sorries

---

## Conclusion

**Option B** (Moderate Modernization) provides the best balance of:
- Safety (keeps critical build check)
- Usability (adds helpful progress feedback)
- Maintainability (removes obsolete code)
- Effort (2-3 hours to implement and test)

**Next Step**: Implement simple version of Option B in this session.

---

**Prepared by**: Research Team (Claude Code)
**Date**: October 18, 2025
**Status**: Proposal ready for implementation
**Estimated Time**: 2-3 hours

