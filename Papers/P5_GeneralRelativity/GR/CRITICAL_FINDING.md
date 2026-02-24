# CRITICAL FINDING: Timeout NOT from Atomic Lemmas!

**Date:** October 4, 2025
**Status:** 🔴 **CRITICAL DISCOVERY**

---

## Discovery

**The compilation timeout is NOT caused by the atomic lemmas!**

### Test Results:

1. **Full Junior Professor patches applied:** TIMEOUT (2+ minutes)
2. **Atomic lemmas with `sorry`:** TIMEOUT (2+ minutes)
3. **Both atomic lemmas sorryed:** TIMEOUT (2+ minutes)

**Conclusion:** The bottleneck is somewhere ELSE in Riemann.lean, not in `compat_r_tt_chart` or `compat_r_rr_chart`.

---

## What This Means

The timeout happens even when:
- `compat_r_tt_chart` = `sorry`
- `compat_r_rr_chart` = `sorry`
- `dCoord_g_via_compat_chart` catchall = `sorry`

This means the expensive operation is **NOT** in the Chart-based optimizations we just added.

---

## Hypothesis

The slowdown might be coming from:

1. **The original `dCoord_g_via_compat_ext` lemma** (Exterior-based version)
   - If this also has 64 expensive cases, it could be the real culprit
   - Lines ~1640-1700 (approximate)

2. **Some other Route A infrastructure**
   - Perhaps `nabla_g_zero_ext` or other _ext lemmas are expensive?

3. **Downstream usage**
   - Maybe something that USES these lemmas is triggering expensive elaboration?

---

## Next Steps

**Option 1:** Check if commenting out the ENTIRE Chart section (lines 1742-1822) makes it compile
**Option 2:** Revert to git HEAD and test if that compiles (it has 14 errors but might at least attempt to compile)
**Option 3:** Check if `dCoord_g_via_compat_ext` (the Exterior version) is the real bottleneck

---

## Request for Guidance

**Junior Professor:** The surgical patches you provided are correct, but they don't fix the timeout because the timeout isn't coming from where we thought.

**Questions:**
1. Should we check the `dCoord_g_via_compat_ext` lemma (Exterior-based)?
2. Is there another known expensive lemma in the Riemann tensor computation?
3. Should we just revert ALL Route A changes and go back to git HEAD?

---

**Files:**
- Current Riemann.lean: Has Chart lemmas with sorries, still times out
- Git HEAD: 14 compilation errors, 24 sorries

**Status:** Blocked - need to identify the ACTUAL bottleneck
