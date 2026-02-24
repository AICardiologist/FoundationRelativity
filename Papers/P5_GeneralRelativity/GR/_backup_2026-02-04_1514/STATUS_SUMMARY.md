# Axiom Calibration Status Summary

**Date:** September 30, 2025
**Branch:** `feat/p0.2-invariants`

---

## Current Achievement: "Level 2.999"

### ✅ COMPLETED
- **Zero project axioms** - `AX_differentiable_hack` ELIMINATED
- **All automatic reasoning axiom-free** - simp uses `@[simp]` versions
- **Schwarzschild.lean (critical path): 0 axioms, 0 sorries**
- **Build passing:** 3078 jobs

### ⚠️ REMAINING WORK
- **Riemann.lean: 5 active sorries to eliminate**

---

## File Status

| File | Axioms | Sorries | Status |
|------|--------|---------|--------|
| Schwarzschild.lean | 0 | 0 | ✅ Publication-ready |
| Riemann.lean | 0 | 5 active + 13 commented | ⚠️ Needs sorry elimination |

---

## The 5 Active Sorries

1. **Line 713:** `dCoord_add` - arbitrary function linearity
2. **Line 719:** `dCoord_sub` - arbitrary function linearity
3. **Line 725:** `dCoord_mul` - arbitrary function product rule
4. **Line 1953:** `mu_t_component_eq` - Stage-2 preview lemma
5. **Line 2010:** `Riemann_alternation` - main alternation proof (Bianchi identity)

---

## Documentation Created

1. **AXIOM_CALIBRATION_FINAL.md** - Achievement summary
2. **PROFESSOR_CONSULT_FINAL_SORRIES.md** - Consultation memo for professor
3. **ELIMINATION_PLAN_TRUE_LEVEL3.md** - Detailed elimination plan
4. **This file** - Status summary

---

## Time Investment

**Phase 1-4 (Axiom Elimination):** 4 hours
- Prove Christoffel differentiability: 1 hour
- Swap @[simp] attributes: 30 min
- Delete axiom: 15 min
- Fix compilation: 2+ hours

**Total to current state:** 4 hours

**Estimated for TRUE LEVEL 3:**
- Optimistic: 4-6 hours
- Realistic: 10-15 hours
- Pessimistic: 20-30 hours

---

## Decision Required

**Question:** Is "Level 2.999" sufficient for axiom calibration?

**Arguments FOR accepting current state:**
- ✅ Zero axioms achieved (main goal)
- ✅ Critical path (Schwarzschild) completely rigorous
- ✅ All automatic reasoning axiom-free
- ⚠️ Remaining sorries are in scaffolding/infrastructure

**Arguments FOR pursuing TRUE LEVEL 3:**
- Highest standard of formalization
- Complete mathematical rigor throughout
- No admitted facts anywhere

**Recommendation:** Consult professor on publication requirements

---

## Next Steps

**Awaiting professor input on:**
1. Is Schwarzschild.lean zero-sorry sufficient?
2. Which sorries are blocking publication?
3. What are "performance issues" with alternation proof?
4. Timeline constraints for publication?

**Once decided:**
- If "Level 2.999" sufficient: ✅ DONE
- If TRUE LEVEL 3 required: Execute ELIMINATION_PLAN_TRUE_LEVEL3.md

---

## Build Verification

```bash
# Verify zero axioms in both files
grep -n "^axiom" Papers/P5_GeneralRelativity/GR/Schwarzschild.lean  # None ✅
grep -n "^axiom" Papers/P5_GeneralRelativity/GR/Riemann.lean        # None ✅

# Count sorries
grep -nE "^\s+sorry" Papers/P5_GeneralRelativity/GR/Schwarzschild.lean | wc -l  # 0 ✅
grep -nE "^\s+(sorry|all_goals \{ left; sorry \})" Papers/P5_GeneralRelativity/GR/Riemann.lean | wc -l  # 18 total (5 active + 13 in comments)

# Build status
lake build Papers.P5_GeneralRelativity.GR.Schwarzschild  # ✅ 3077 jobs
lake build Papers.P5_GeneralRelativity.GR.Riemann        # ✅ 3078 jobs
```

---

**Status:** ⏸️ Awaiting professor guidance on path forward

🎯 **Achievement:** Zero axioms - Final push to zero sorries pending decision
