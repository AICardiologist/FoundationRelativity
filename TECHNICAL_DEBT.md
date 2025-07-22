# Technical Debt Documentation

## Overview
This document tracks technical debt accumulated during Sprint S6 (SpectralGap implementation) and planned resolution strategies.

## 🔧 Current Technical Debt

### High Priority

#### 1. SpectralGap Placeholder Implementation
**File**: `SpectralGap/HilbertSetup.lean:57`  
**Issue**: `gap` field uses `True` placeholder instead of real spectrum proof  
**Root Cause**: mathlib 4.3.0 compatibility limitations
- `spectrum_zero_eq_singleton` lemma doesn't exist in v4.3.0
- Spectrum imports cause type class synthesis timeouts (>20000 heartbeats)
- `MulAction ℂ BoundedOp` synthesis fails

**Current State**:
```lean
structure SpectralGapOperator where
  -- ...
  gap_lt  : a < b                                    -- ✅ Real proof
  gap     : True  -- TODO: Real spectrum condition   -- ❌ Placeholder
```

**What We Tried (Failed Approaches)**:
1. ❌ **Direct import approach**: `import Mathlib.Analysis.NormedSpace.Spectrum`
   - **Result**: Type class synthesis timeouts (>20000 heartbeats)
   - **Error**: `failed to synthesize Nontrivial BoundedOp` and `MulAction ℂ BoundedOp`
   
2. ❌ **Heavy instance provisioning**: Added multiple manual instances
   - **Attempts**: `NeZero (1 : BoundedOp)`, various nontrivial instances
   - **Result**: Still timed out, created more synthesis loops
   
3. ❌ **Lemma name variations**: Tried multiple spectrum lemma names
   - **Attempts**: `spectrum_zero_eq_singleton`, `Spectrum.zero_eq_singleton` 
   - **Root cause**: Lemma simply doesn't exist in mathlib 4.3.0 (commit f04afed5ac)
   
4. ❌ **Parser syntax issues**: Used doc-string syntax in wrong context
   - **Error**: `unexpected token '/--'` - doc-strings must precede commands
   - **Fix**: Changed to `/-! ... -/` for regular comments
   
5. ❌ **CI parameter issues**: Used deprecated `lean-version` parameter
   - **Warning**: "Unexpected input 'lean-version'" in GitHub Actions
   - **Fix**: Removed parameter, let lean-action auto-detect

**Resolution Options**:
1. **Route A**: Upgrade mathlib to 4.4.0+ (has `Spectrum.zero_eq_singleton`)
   - **Risk**: Breaking changes, longer CI builds, requires Lean 4.4.0+
2. **Route B**: Implement local spectrum lemma (Math-AI's recommendation) ⭐
   - **Benefit**: Avoids import issues, educational value, stable builds
3. **Route C**: Wait for mathlib improvements
   - **Downside**: Indefinite blocking of real mathematical content

**Recommended**: Route B - Local spectrum proof as suggested by Math-AI

#### 2. Unused Instance Cleanup
**Files**: Various (to be identified)  
**Issue**: Old `NeZero (1 : BoundedOp)` instance attempts may still exist  
**Root Cause**: Multiple failed attempts to fix spectrum import issues  
**Resolution**: Remove old NeZero instances now that `ContinuousLinearMap.nontrivial` works

### Medium Priority

#### 3. CI Workflow Parameter Warning
**File**: `.github/workflows/ci.yml`  
**Issue**: GitHub Actions warns about unexpected `lean-version` parameter  
**Status**: ✅ FIXED (removed deprecated parameter)
**Details**: Was causing warnings but not blocking builds

#### 4. Documentation Inconsistencies  
**Issue**: Some docs still reference "beyond ρ-scale" instead of "ρ=3 (AC_ω)"  
**Status**: ✅ PARTIALLY FIXED (main docs updated)  
**Remaining**: Check for any missed references in comments or auxiliary docs

### Low Priority

#### 5. Comment Style Inconsistencies
**File**: `SpectralGap/HilbertSetup.lean`  
**Issue**: Mixed comment styles (some use `/-!`, others use `--`)  
**Resolution**: Standardize on `/-!` for block comments, `--` for line comments

## 📋 Resolution Plan

### Sprint S6 Cleanup (Immediate)

**Week 1**: Core Infrastructure Cleanup
- [ ] **TD-1**: Implement local spectrum lemma (Route B)
  ```lean
  lemma spectrum_zero_local :
      spectrum ℂ (0 : BoundedOp) = {0} := by
    -- Implement Math-AI's standalone proof
    sorry
  ```
- [ ] **TD-2**: Remove old NeZero instance attempts
- [ ] **TD-5**: Standardize comment styles

**Week 2**: Testing and Validation  
- [ ] Verify all technical debt fixes don't break existing functionality
- [ ] Update tests to cover spectrum lemma
- [ ] Run full CI suite with improvements

### Milestone C Integration

**During Milestone C Development**:
- [ ] **TD-1 Extension**: Extend local spectrum approach to non-trivial operators
- [ ] Add comprehensive spectrum testing
- [ ] Document the local spectrum strategy for future maintainers

## 🚫 Anti-Patterns to Avoid

Based on our Sprint S6 experience:

1. **Don't**: Import heavy mathlib modules without checking compatibility first
2. **Don't**: Use doc-string syntax (`/-- ... -/`) for regular comments
3. **Don't**: Accumulate multiple failed instance attempts - clean up immediately
4. **Do**: Test builds locally before pushing CI-breaking changes
5. **Do**: Document workarounds clearly when forced to use placeholders

## 📊 Technical Debt Metrics

### Current Status
- **High Priority Items**: 2 (1 major, 1 cleanup)
- **Medium Priority Items**: 2 (both documentation-related)  
- **Low Priority Items**: 1 (style consistency)
- **Estimated Resolution Time**: 1-2 weeks

### Success Criteria
- [ ] All `True` placeholders replaced with real proofs
- [ ] Zero unused instances or imports
- [ ] Clean CI runs without warnings
- [ ] Consistent code style throughout SpectralGap module

## 🔄 Maintenance Strategy

### Prevention
1. **Pre-commit hooks**: Check for new `True` placeholders
2. **CI enforcement**: Fail builds with import warnings  
3. **Code review**: Require justification for any new technical debt
4. **Documentation**: Always document workarounds with TODO comments

### Monitoring
- Weekly review of technical debt status during active sprints
- Monthly cleanup sprints for accumulated debt
- Quarterly assessment of whether workarounds can be resolved

## 🔍 Debugging Journey: What Went Wrong and Why

### The Spectrum Import Disaster

**Timeline of Failures** (to help future developers recognize similar patterns):

#### Day 1: The Optimistic Beginning
```lean
-- This looked so simple...
import Mathlib.Analysis.NormedSpace.Spectrum

lemma spectrum_zero : spectrum ℂ (0 : BoundedOp) = {0} := by
  exact spectrum_zero_eq_singleton -- This should work, right?
```
**Result**: `unknown constant spectrum_zero_eq_singleton` ❌

#### Day 2: The Great Lemma Hunt  
**What we tried**: Searched through mathlib files, tried variations:
- `Spectrum.zero_eq_singleton` 
- `spectrum.zero_eq_singleton`
- `spectralRadius_zero` (exists, but wrong lemma)
- Various capitalization combinations

**Discovery**: The lemma **literally doesn't exist** in mathlib 4.3.0
```bash
$ grep -R "spectrum_zero_eq_singleton" .lake/packages/mathlib
[no results]
```

#### Day 3-4: The Type Class Timeout Hell
**Problem**: Even importing spectrum caused cascading failures:
```lean
import Mathlib.Analysis.NormedSpace.Spectrum

-- This simple line would fail:
instance : Nontrivial BoundedOp := by infer_instance
-- Error: (deterministic) timeout at 'typeclass', maximum number of heartbeats (20000) has been reached
```

**Why**: The spectrum file pulls in ~400 additional modules including:
- Matrix norms
- Banach-Alaoglu theorem  
- Functional calculus theory
- Heavy algebraic hierarchy

This created exponential type class search spaces.

#### Day 5: The Instance Multiplication Strategy (Failed)
**Desperate attempt**: "Maybe we need MORE instances!"
```lean
instance : NeZero (1 : BoundedOp) := ⟨by simp⟩
instance : Nontrivial BoundedOp := ContinuousLinearMap.nontrivial  
instance : MulAction ℂ BoundedOp := by infer_instance
-- Added 5+ more instances...
```
**Result**: Made timeouts WORSE by creating synthesis loops ❌

#### Day 6: The Parser Trap
```lean
/-- This comment broke everything! -/
open Complex
-- Error: unexpected token '/--'
```
**Discovery**: Doc-strings (`/-- ... -/`) must immediately precede commands (def, lemma, etc.)
**Fix**: Use `/-! ... -/` for regular comments

### Root Cause Analysis

**The Real Problem**: mathlib 4.3.0 is missing critical spectrum infrastructure
- Spectrum theory was incomplete in this version
- Heavy imports create type class synthesis storms  
- No `spectrum_zero_eq_singleton` lemma available
- Complex number actions on operators poorly supported

**Why This Was So Hard to Diagnose**:
1. **Misleading documentation**: Lean 4 docs show spectrum usage but don't specify mathlib version requirements
2. **Cascading failures**: Import errors masked the real issue (missing lemma)
3. **Timeout errors**: Generic "heartbeat exceeded" doesn't point to root cause
4. **Version lag**: Project pinned to mathlib 4.3.0 for stability, but spectrum theory needed 4.4.0+

## 📝 Lessons Learned

### Sprint S6 Insights - Hard-Won Knowledge
1. **Check lemma existence FIRST**: Use `grep -R "lemma_name" .lake/packages/mathlib` before designing proofs
2. **Mathlib version matters critically**: Don't assume features exist in older versions
3. **Import weight**: Some mathlib modules pull in hundreds of dependencies
4. **Local proofs >> import fights**: Math-AI was right - local lemmas often better than heavy imports
5. **Timeout diagnostics**: Type class timeouts usually mean "dependency hell", not "need more instances"
6. **Comment syntax matters**: `/--` has special meaning, use `/-!` for regular comments
7. **Incremental development**: Math-AI's staged milestones (A→B→C→D) prevented total disaster

### For Future Developers

**🚨 RED FLAGS - Stop and reconsider if you see:**
- Type class synthesis timeouts after adding imports
- "Unknown constant" for lemmas you found in online docs  
- CI builds suddenly taking 8+ minutes
- Need to add 3+ manual instances to make something work

**✅ SAFE APPROACHES:**
```bash
# Before committing to any mathlib lemma:
grep -R "lemma_name" .lake/packages/mathlib

# Before importing heavy modules:
lake build --dry-run | wc -l  # Check how many files would build

# Test locally first:
lake build SpectralGap.HilbertSetup -K 100000  # With generous heartbeats
```

**🛡️ DEFENSIVE STRATEGIES:**
- Always implement a "Plan B" (local lemma approach)
- Budget 2x expected time for any new mathlib integration
- Document workarounds immediately, don't let them accumulate
- Use staged implementation (like Math-AI's milestone approach)

### For Future Sprints
- **Research phase**: Dedicate 1-2 days to mathlib compatibility research BEFORE coding
- **Local-first philosophy**: Prefer self-contained proofs over heavy imports
- **Debt tracking**: Set up technical debt documentation from day 1
- **Time budget**: Reserve 15-25% of sprint time for import/compatibility issues
- **Rollback readiness**: Always have a working fallback before attempting risky imports

## 🚨 Emergency Troubleshooting Quick Reference

**When you see type class synthesis timeouts:**
```bash
# 1. Check what you just imported
git diff HEAD~1 -- "*.lean" | grep "import"

# 2. Remove suspect imports and test
# 3. If timeout persists, check for circular instance dependencies
```

**When you see "unknown constant" errors:**
```bash
# 1. Verify lemma exists in your mathlib version
grep -R "lemma_name" .lake/packages/mathlib

# 2. Check mathlib version
git -C .lake/packages/mathlib rev-parse --short HEAD

# 3. Search mathlib docs for alternative names
# 4. Consider local proof approach
```

**When CI suddenly becomes slow:**
```bash
# 1. Check if mathlib cache is working
# 2. Look for new heavy imports in recent commits
# 3. Consider reverting to known-good state

# Emergency rollback command:
git reset --hard HEAD~N  # Replace N with number of problematic commits
```

**When in doubt:**
1. 🛑 **STOP** adding more instances/imports
2. 📚 **RESEARCH** the mathlib compatibility first
3. 💬 **ASK** Math-AI or team for guidance before continuing
4. 📝 **DOCUMENT** whatever approach you take

---

*Technical debt tracking started: Sprint S6 Milestone B completion*  
*Next review: Milestone C kickoff*