# Sharing Guide: Which Files to Show to Whom
**Date**: October 22, 2025
**Purpose**: Quick reference for sharing documentation with collaborators

---

## For Junior Professor (JP) - Tactical Implementation Help

**Primary document**:
- ✅ **`TACTICAL_REPORT_FOR_JP_OCT22.md`** (just created)
  - Complete sorry inventory with code context
  - Dependency graph
  - 4-week tactical workflow
  - Integration plan for 6 micro-lemma skeletons
  - 5 specific questions for JP

**Supporting documents**:
- `REPORT_TO_JP_OCT22_RECURSION_FIXES.md` (recursion fix details)
- `JP_EXPLANATION_CASE_G_OCT22.md` (technical explanation of "case G")
- `FINAL_STATUS_OCT22_SUCCESS.md` (build success verification)

**Code files**:
- `Riemann.lean` (main file, compiles cleanly)
- `Riemann.lean.backup_before_deletion` (Step 6 code backup for restoration)

---

## For Senior Professor (SP) - Mathematical Validation

**Primary document**:
- ✅ **`MEMO_TO_SENIOR_PROFESSOR_OCT22.md`** (just created)
  - Mathematical proof strategy overview
  - 15 specific validation questions
  - Textbook references (MTW, Wald, Carroll)
  - Physical interpretation sanity checks
  - Counterexample verification request

**Supporting documents**:
- `Riemann.lean` (to see actual formalization)
- Sections to highlight:
  - Lines 5783-5791: `ricci_identity_on_g_rθ_ext` (critical path blocker)
  - Lines 5816-5834: `Riemann_swap_a_b` (antisymmetry derivation)
  - Lines 8415-8497: Γ₁ approach
  - Lines 8507-8523: False lemma with counterexample

---

## For General Context (All Collaborators)

**Quick status**:
- `FINAL_STATUS_OCT22_SUCCESS.md` (executive summary)

**Process guardrail**:
- Rule: Do not declare "build OK" until `lake build Papers.P5_GeneralRelativity.GR.Riemann` exits with 0 errors
- Documented in: `FINAL_STATUS_OCT22_SUCCESS.md` lines 127-133

---

## Summary of Current Status

**Build status**: ✅ **SUCCESS** (0 errors, 0 recursion depth errors)

**Metrics**:
- Compilation errors: 0
- Recursion errors: 0 (all 6 sites fixed)
- Axioms: 0
- Active sorries: 17 (catalogued with full context)
- Commented-out sorries: 5 (archived, lines 1996-2088)

**Critical path**:
1. Complete `ricci_identity_on_g_rθ_ext` (line 5790) using JP's `suffices` pattern
2. Fill 6 payload conversion micro-lemmas (JP offered skeletons)
3. Prove differentiability lemmas (lines 8421, 8423)
4. Propagate to downstream lemmas (antisymmetry, general cases)

**Timeline estimate**: 4-6 weeks of tactical work (assuming mathematical approach is sound)

**Next step**: Await feedback from JP and SP before proceeding with implementation

---

## Files Created This Session

1. `TACTICAL_REPORT_FOR_JP_OCT22.md` - Detailed tactical guide for JP ✅
2. `MEMO_TO_SENIOR_PROFESSOR_OCT22.md` - Mathematical validation request for SP ✅
3. `SHARING_GUIDE_OCT22.md` - This file ✅

**Previous session files** (still relevant):
- `FINAL_STATUS_OCT22_SUCCESS.md` - Build success summary
- `REPORT_TO_JP_OCT22_RECURSION_FIXES.md` - Recursion fix comprehensive report
- `JP_EXPLANATION_CASE_G_OCT22.md` - "case G" technical explanation
- `UPDATE_TO_JP_CASE_G_SOURCE.md` - Diagnostic experiments
- `Riemann.lean.backup_before_deletion` - Step 6 code backup

---

**Prepared by**: Claude Code (Assistant)
**Date**: October 22, 2025
