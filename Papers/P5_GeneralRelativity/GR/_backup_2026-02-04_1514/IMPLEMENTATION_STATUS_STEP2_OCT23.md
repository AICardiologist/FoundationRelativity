# Implementation Status: algebraic_identity - Steps 2-6 Structure Complete
**Date**: October 23, 2025
**Status**: ✅ Steps 2-6 structure fully implemented and compiling
**Build**: ✅ 0 errors, 80 total sorries
**Lines**: Riemann.lean:6450-6549 (Steps 2-6 scaffolding)

---

## ✅ What's Complete

### Step 2: Collector Bindings (Lines 6455-6494)

**Complete implementation** of JP's collector pattern for both branches:

#### A-branch collectors (lines 6456-6474):
```lean
set Gab  : Idx → ℝ := fun ρ => g M ρ b r θ
set Aμ   : Idx → ℝ := fun ρ => dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
set Bν   : Idx → ℝ := fun ρ => dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
set Cμ   : Idx → ℝ := fun ρ => sumIdx (fun lam => Γtot M r θ ρ μ lam * Γtot M r θ lam ν a)
set Dν   : Idx → ℝ := fun ρ => sumIdx (fun lam => Γtot M r θ ρ ν lam * Γtot M r θ lam μ a)
set Pμ   : Idx → ℝ := fun ρ => Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ
set Qν   : Idx → ℝ := fun ρ => Γtot M r θ ρ μ a * dCoord ν (fun r θ => g M ρ b r θ) r θ

have hCollect_a := sumIdx_collect_comm_block_with_extras Gab Aμ Bν Cμ Dν Pμ Qν
```

✅ **Syntax fixes applied**:
- Changed `let` to `set` (fixes "unsolved goals" error)
- Used ASCII underscores instead of unicode superscripts for b-branch variables

#### B-branch collectors (lines 6476-6494):
```lean
set Gba    : Idx → ℝ := fun ρ => g M a ρ r θ
set Amu_b  : Idx → ℝ := fun ρ => dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ
set Bnu_b  : Idx → ℝ := fun ρ => dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ
set Cmu_b  : Idx → ℝ := fun ρ => sumIdx (fun lam => Γtot M r θ ρ μ lam * Γtot M r θ lam ν b)
set Dnu_b  : Idx → ℝ := fun ρ => sumIdx (fun lam => Γtot M r θ ρ ν lam * Γtot M r θ lam μ b)
set Pmu_b  : Idx → ℝ := fun ρ => Γtot M r θ ρ ν b * dCoord μ (fun r θ => g M a ρ r θ) r θ
set Qnu_b  : Idx → ℝ := fun ρ => Γtot M r θ ρ μ b * dCoord ν (fun r θ => g M a ρ r θ) r θ

have hCollect_b := sumIdx_collect_comm_block_with_extras Gba Amu_b Bnu_b Cmu_b Dnu_b Pmu_b Qnu_b
```

✅ Compiles perfectly with corrected syntax

---

### Steps 3-6: Algebraic Scaffolding (Lines 6496-6549)

Created proof scaffolding with proper structure:

**Step 3** (lines 6496-6504): A-branch payload cancellation stub
- Formula: Show `sumIdx(Pμ - Qν) + Γ∂g terms = 0`
- TODO: Apply `hCollect_a` and show cancellation with `C_terms_a`
- Status: ⚠️ Sorry (line 6504)

**Step 4** (lines 6506-6513): B-branch payload cancellation stub
- Formula: Show `sumIdx(Pmu_b - Qnu_b) + Γ∂g terms = 0`
- TODO: Apply `hCollect_b` and show cancellation with `C_terms_b`
- Status: ⚠️ Sorry (line 6513)

**Step 5** (lines 6515-6520): Clairaut's theorem
```lean
have hmixed :
  dCoord μ (fun r θ => dCoord ν (fun r θ => g M a b r θ) r θ) r θ
  = dCoord ν (fun r θ => dCoord μ (fun r θ => g M a b r θ) r θ) r θ := by
  exact dCoord_commute_for_g_all M r θ a b μ ν
```
✅ **This step is PROVEN** (line 6520)

**Step 6a** (lines 6522-6533): A-branch Riemann recognition
- Formula: Match `∑_ρ g_ρb * ((∂Γ)ρνa + (ΓΓ)ρνa)` to `-Riemann M r θ b a μ ν`
- TODO: Use `Riemann_contract_first` and `sumIdx_collect6`
- Status: ⚠️ Sorry (line 6533)

**Step 6b** (lines 6535-6544): B-branch Riemann recognition
- Formula: Match `∑_ρ g_aρ * ((∂Γ)ρνb + (ΓΓ)ρνb)` to `-Riemann M r θ a b μ ν`
- TODO: Use `Riemann_contract_first` and `sumIdx_collect6`
- Status: ⚠️ Sorry (line 6544)

**Final calc structure** (lines 6546-6549):
- TODO: Wire all lemmas together using calc blocks with algebraic reshaping
- Status: ⚠️ Sorry (line 6549)

---

## 📊 Sorry Breakdown

**Total sorries**: 80 (from build output)

### From Steps 1A & 1B (Previously documented):
- ~68 differentiability sorries (C²-lite + sumIdx terms + individual terms)

### New from Steps 2-6 (This session):
- Line 6504: `hPayload_a` - A-branch payload cancellation
- Line 6513: `hPayload_b` - B-branch payload cancellation
- Line 6533: `hRa` - A-branch Riemann recognition
- Line 6544: `hRb` - B-branch Riemann recognition
- Line 6549: Final calc block - Wire all steps together
- Line 6587: `ricci_identity_on_g_rθ_ext` - Top-level theorem wrapper

**Total new sorries**: 6 (5 in algebraic_identity, 1 in wrapper theorem)

---

## 🎯 Key Achievements

1. ✅ **Step 2 collectors**: Both a-branch and b-branch collectors compile with correct syntax
2. ✅ **Step 5 Clairaut**: Fully proven using `dCoord_commute_for_g_all`
3. ✅ **Steps 3-6 scaffolding**: All `have` statements properly typed and documented
4. ✅ **Build success**: 0 compilation errors, clean structure for remaining algebraic work

---

## 🎓 Technical Lessons Learned

### Lean 4 Syntax:
- **Use `set` not `let`** for local definitions that need to be referenced in proofs
- **No unicode superscripts** in identifiers (use underscores: `Amu_b` not `Aμᵇ`)
- **`exact` vs `simpa using`**: For direct lemma application, `exact` is cleaner

### Proof Architecture:
- **Collector pattern works**: JP's `sumIdx_collect_comm_block_with_extras` bindings compile correctly
- **Stub first, prove later**: Scaffolding with `sorry` allows iterative development
- **Step 5 is free**: Clairaut's theorem already exists, just needs direct application

---

## 🚧 What Remains

### To Complete `algebraic_identity`:

**Step 3 (hPayload_a)**:
- Expand `hCollect_a` result
- Show `∑(Pμ - Qν)` matches the Γ∂g terms from `C_terms_a` expansion
- Use `sumIdx_congr` + `ring` to finish

**Step 4 (hPayload_b)**:
- Mirror of Step 3 for b-branch
- Expand `hCollect_b` result
- Use `sumIdx_congr` + `ring` to finish

**Step 6 (hRa & hRb)**:
- Unfold `Riemann` and `RiemannUp` definitions
- Use `Riemann_contract_first` to rewrite `∑_ρ g_ρb * RiemannUp_ρaμν` as `Riemann_baμν`
- Apply `sumIdx_collect6` for the (2 ∂Γ + 4 ΓΓ) structure
- Use `g_symm` for index swapping where needed

**Final calc block**:
- Chain: `hPμ_full` → `hPν_full` → `hCollect_a` → `hCollect_b` → `hPayload_a` → `hPayload_b` → `hmixed` → `hRa` → `hRb`
- Use JP's flatten/fold lemmas (`flatten₄₁`, `fold_sub_right`, etc.) to reshape expressions
- Apply `ring` at strategic points to simplify scalar algebra

---

## 💡 Recommendations

### Option A: Continue with Steps 3-6 Proofs (Recommended)

The structure is in place. Complete the algebraic manipulations:

**Estimated effort**: 3-4 hours
- Step 3: 30 min (straightforward collector + ring)
- Step 4: 30 min (mirror of Step 3)
- Step 6a & 6b: 1-2 hours (Riemann definition matching, needs careful index work)
- Final calc: 1 hour (chaining with algebraic reshaping)

**Risk**: Low - all lemmas exist, just needs patient algebra

---

### Option B: Write Report to JP

If any of Steps 3-6 proves unexpectedly difficult, or if additional collector lemmas are needed, write a diagnostic report.

**When to escalate**:
- If `sumIdx_collect_comm_block_with_extras` output doesn't match expected form
- If `Riemann_contract_first` doesn't exist or has wrong signature
- If flatten/fold lemmas are missing or don't chain properly

---

### Option C: Clean Differentiability Sorries

Prove the ~68 differentiability sorries from Steps 1A & 1B in parallel.

**Estimated effort**: 4-6 hours (repetitive but straightforward)

**Benefit**: Get to 0 sorries total

---

## 📝 Files Modified

- `Riemann.lean`: Lines 6450-6549 (Steps 2-6 structure)
- `IMPLEMENTATION_STATUS_STEP1_OCT23.md`: Previous status (Steps 1A & 1B)
- `IMPLEMENTATION_STATUS_STEP2_OCT23.md`: This status report

---

## 🎉 Bottom Line

**Steps 1A & 1B are DONE** (360 lines, ~68 differentiability sorries).

**Steps 2-6 structure is DONE** (100 lines, 5 algebraic sorries + 1 wrapper).

**Step 5 Clairaut is PROVEN** (0 sorries).

**Next**: Complete the 5 remaining algebraic proofs in Steps 3-6 to close `algebraic_identity`.

---

**Build Status**: `lake build Papers.P5_GeneralRelativity.GR.Riemann`
```
Build completed successfully (3078 jobs).
✅ 0 errors
⚠️  80 sorries total (~68 differentiability + 6 algebraic + ~6 other)
```

**Ready for**: Steps 3-6 algebraic completion OR differentiability cleanup OR both in parallel!
