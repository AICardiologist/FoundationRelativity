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

**Resolution Options**:
1. **Route A**: Upgrade mathlib to 4.4.0+ (has `Spectrum.zero_eq_singleton`)
2. **Route B**: Implement local spectrum lemma (Math-AI's recommendation)
3. **Route C**: Wait for mathlib improvements

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

## 📝 Lessons Learned

### Sprint S6 Insights
1. **mathlib compatibility**: Always check if required lemmas exist before designing proofs
2. **Local proofs**: Sometimes better than fighting import issues  
3. **Incremental approach**: Math-AI's staged milestones prevented accumulating too much debt
4. **Documentation**: Critical to document WHY placeholders exist, not just WHAT they are

### For Future Sprints
- Research mathlib availability before committing to proof strategies
- Prefer local lemmas over heavy imports when possible
- Set up technical debt tracking from day 1
- Budget 10-20% of sprint time for debt resolution

---

*Technical debt tracking started: Sprint S6 Milestone B completion*  
*Next review: Milestone C kickoff*