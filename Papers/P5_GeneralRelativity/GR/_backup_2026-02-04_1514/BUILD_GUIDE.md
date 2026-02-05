# Build Guide - Schwarzschild Formalization

**Project:** Schwarzschild Spacetime Curvature Formalization (Lean 4)
**Location:** `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/`

---

## Quick Start

### Standard Build

```bash
cd /Users/quantmann/FoundationRelativity
lake build Papers.P5_GeneralRelativity.GR.Schwarzschild
lake build Papers.P5_GeneralRelativity.GR.Riemann
lake build Papers.P5_GeneralRelativity.GR.Invariants
```

### After Infrastructure Changes (Recommended)

If you've modified core definitions (metric, Christoffel symbols, Riemann tensor):

```bash
cd /Users/quantmann/FoundationRelativity
lake clean
lake exe cache get
lake build Papers.P5_GeneralRelativity.GR.Schwarzschild
lake build Papers.P5_GeneralRelativity.GR.Riemann
lake build Papers.P5_GeneralRelativity.GR.Invariants
```

**Why this sequence?**
- `lake clean`: Removes stale build artifacts
- `lake exe cache get`: Downloads fresh Mathlib cache (saves ~30 minutes)
- Sequential builds: Ensures dependencies are built in correct order

---

## Build Times (Typical)

**On standard hardware (M1/M2 Mac or equivalent):**

| File | Clean Build | Incremental Build |
|------|-------------|-------------------|
| Schwarzschild.lean | ~30s | ~5s |
| Riemann.lean | ~90s | ~15s |
| Invariants.lean | ~20s | ~5s |

**Total clean build:** ~2-3 minutes (after cache download)

---

## File Dependencies

```
Schwarzschild.lean (geometry, metric, Christoffel symbols)
    ↓
Riemann.lean (curvature tensor, symmetries, Ricci)
    ↓
Invariants.lean (Einstein tensor, Kretschmann scalar)
```

**Import structure:**
- `Riemann.lean` imports `Schwarzschild.lean`
- `Invariants.lean` imports both `Schwarzschild.lean` and `Riemann.lean`

**Build order matters!** Always build in sequence: Schwarzschild → Riemann → Invariants.

---

## Verifying Build Success

### Check for Errors

```bash
lake build Papers.P5_GeneralRelativity.GR.Riemann 2>&1 | grep "error:"
```

**Expected:** No output (no errors)

### Check for Sorries

```bash
grep -c "^  sorry" GR/Riemann.lean
grep -c "sorry" GR/Invariants.lean
```

**Expected:**
- Riemann.lean: 1 (deferred `Riemann_pair_exchange` at line 5116)
- Invariants.lean: 0

### Check for Warnings

Common harmless warnings:
- `try 'simp' instead of 'simpa'` - linter suggestion (non-blocking)
- `This simp argument is unused` - optimization hint (non-blocking)

**These do not affect correctness.**

---

## Common Build Issues

### Issue 1: Timeout During Build

**Symptom:** Build hangs for >5 minutes

**Cause:** Expensive `unfold ... ring` proofs or global simp loops

**Fix:**
1. Check recent changes to simp lemmas
2. Ensure heavy lemmas are in `@[local simp]` blocks, not global
3. Run `lake clean` to clear stale cache

### Issue 2: Type Mismatch After Metric Changes

**Symptom:** `type mismatch` errors in Riemann.lean after changing `g` or `gInv`

**Cause:** Cached .olean files don't match new definitions

**Fix:**
```bash
lake clean
lake build Papers.P5_GeneralRelativity.GR.Schwarzschild
lake build Papers.P5_GeneralRelativity.GR.Riemann
```

### Issue 3: "Unknown identifier" Errors

**Symptom:** `unknown identifier 'Riemann_swap_a_b_ext'`

**Cause:** Dependency not built or import missing

**Fix:**
1. Check imports at top of file
2. Rebuild Schwarzschild.lean and Riemann.lean in order
3. Verify lemma names match (case-sensitive!)

---

## Controlled Rewriting Pattern

**Our proof strategy** (explained for contributors):

We avoid expensive global simplification. Instead, we use **controlled rewriting**:

```lean
-- ❌ SLOW: Global simp unfolds everything
simp [Riemann, RiemannUp, Γtot, g]

-- ✅ FAST: Controlled sequence
unfold Riemann RiemannUp          -- Expand only what we need
simp only [sumIdx_expand]         -- Expand sums (deterministic)
rw [deriv_Γ_r_tt M r hr0 hf hr2M] -- Apply specific derivative lemma
simp only [Γ_r_tt, Γ_t_tr]       -- Substitute specific Γ values
field_simp [hr0, hf]              -- Rational simplification
ring                              -- Polynomial close
```

**Why this works:**
- Each step is **deterministic** (no backtracking)
- Only unfolds what's needed (avoids exponential expansion)
- Builds fast and stays fast as code grows

**See:** Riemann.lean lines 3600-4000 for examples (R_rtrt_eq, R_θtθt_eq, etc.)

---

## Performance Tips for New Lemmas

### 1. Keep Simp Sets Local

```lean
section MyProof
-- Heavy simp lemmas only active in this section
attribute [local simp] sumIdx_Γ_g_left sumIdx_Γ_g_right

lemma my_lemma := by
  simp only [...]  -- Uses local simp set
  ring

end MyProof
-- Heavy lemmas no longer in global simp set
```

### 2. Use `simp only` Instead of `simp`

```lean
-- ❌ UNPREDICTABLE: Uses all global simp lemmas
simp

-- ✅ DETERMINISTIC: Uses exactly these lemmas
simp only [Riemann_first_equal_zero, sq_neg, pow_two]
```

### 3. Factor Out Derivative Computations

```lean
-- Compute derivatives once, name the result
have dΓ_rtt : deriv (fun s => Γtot M s θ r t t) r = ... := by
  rw [deriv_Γ_r_tt M r hr0 hf hr2M]
  simp [Γ_r_tt, f]

-- Reuse in multiple places
rw [dΓ_rtt]
```

---

## Testing Changes

### After Modifying Schwarzschild.lean

```bash
lake build Papers.P5_GeneralRelativity.GR.Schwarzschild
lake build Papers.P5_GeneralRelativity.GR.Riemann      # Check downstream
```

### After Modifying Riemann.lean

```bash
lake build Papers.P5_GeneralRelativity.GR.Riemann
lake build Papers.P5_GeneralRelativity.GR.Invariants  # Check downstream
```

### After Adding New Simp Lemmas

```bash
lake clean  # Clear cache to avoid stale simp sets
lake build Papers.P5_GeneralRelativity.GR.Schwarzschild
lake build Papers.P5_GeneralRelativity.GR.Riemann
```

---

## CI/Automation Recipe

For automated testing (GitHub Actions, etc.):

```bash
#!/bin/bash
set -e  # Exit on error

cd /Users/quantmann/FoundationRelativity

# 1. Get fresh Mathlib cache
lake exe cache get

# 2. Build in dependency order
lake build Papers.P5_GeneralRelativity.GR.Schwarzschild
lake build Papers.P5_GeneralRelativity.GR.Riemann
lake build Papers.P5_GeneralRelativity.GR.Invariants

# 3. Verify no unexpected sorries
RIEMANN_SORRIES=$(grep -c "^  sorry" Papers/P5_GeneralRelativity/GR/Riemann.lean || true)
INVARIANTS_SORRIES=$(grep -c "sorry" Papers/P5_GeneralRelativity/GR/Invariants.lean || true)

if [ "$RIEMANN_SORRIES" -ne 1 ]; then
  echo "ERROR: Expected 1 sorry in Riemann.lean, found $RIEMANN_SORRIES"
  exit 1
fi

if [ "$INVARIANTS_SORRIES" -ne 0 ]; then
  echo "ERROR: Expected 0 sorries in Invariants.lean, found $INVARIANTS_SORRIES"
  exit 1
fi

echo "✅ All builds successful, sorry count correct"
```

---

## File Structure

```
GR/
├── Schwarzschild.lean    (~1800 lines) - Metric, Christoffels, basic helpers
├── Riemann.lean          (~5700 lines) - Riemann tensor, symmetries, Ricci
├── Invariants.lean       (~330 lines)  - Einstein, Kretschmann scalars
├── Interfaces.lean                     - Abstract interfaces (not used)
│
├── SESSION_*.md                        - Development history
├── SYMMETRY_COMPLETE_REPORT.md         - Symmetry implementation summary
├── EINSTEIN_KRETSCHMANN_COMPLETE.md    - Invariants completion summary
└── BUILD_GUIDE.md                      - This file
```

---

## Key Sections in Each File

### Schwarzschild.lean
- **Lines 15-30:** Index type and basic operations
- **Lines 60-120:** Schwarzschild function `f(M,r)` and helpers
- **Lines 130-180:** Exterior domain definition and properties
- **Lines 300-500:** Metric tensor `g_{μν}` and inverse `g^{μν}`
- **Lines 600-900:** Christoffel symbols Γ^μ_{νρ} (10 non-zero)
- **Lines 1000-1800:** Derivative lemmas for Christoffels

### Riemann.lean
- **Lines 1-1300:** Infrastructure (sumIdx, dCoord, helpers)
- **Lines 1300-3800:** Riemann component computations (6 principal values)
- **Lines 3800-4000:** Riemann antisymmetry lemmas
- **Lines 4900-5000:** Ricci off-diagonal sum lemmas
- **Lines 5200-5600:** Ricci diagonal cases (all = 0)
- **Lines 5038-5170:** **Symmetry section** (pair-exchange, orientation lemmas)
- **Lines 5600+:** Main Ricci_zero_ext theorem

### Invariants.lean
- **Lines 13-40:** RicciScalar, Einstein definitions and vanishing theorems
- **Lines 43-127:** Kretschmann definition and six-block structural lemma
- **Lines 130-305:** Six block value computations
- **Lines 306-316:** Kretschmann_exterior_value (K = 48M²/r⁶)

---

## Getting Help

**Common questions:**
1. **Build timeout?** → Use controlled rewriting pattern (see above)
2. **Type mismatch?** → Run `lake clean` and rebuild in order
3. **Unknown identifier?** → Check imports and build dependencies first

**Documentation:**
- See `SYMMETRY_COMPLETE_REPORT.md` for symmetry implementation details
- See `EINSTEIN_KRETSCHMANN_COMPLETE.md` for invariants details
- See session reports (`SESSION_*.md`) for development history

---

## Status Summary

**Current State (October 4, 2025):**
- ✅ Schwarzschild.lean: Complete, 0 sorries
- ✅ Riemann.lean: 1 deferred sorry (non-blocking)
- ✅ Invariants.lean: Complete, 0 sorries

**All physical results proven:**
- Ricci tensor: R_{μν} = 0 ✅
- Einstein tensor: G_{μν} = 0 ✅
- Kretschmann scalar: K = 48M²/r⁶ ✅

**Build status:** Fast, deterministic, production-ready ✅

---

**Maintained by:** Research Team - Schwarzschild Formalization Project
**Last Updated:** October 4, 2025
**Lean Version:** 4.x with Mathlib
