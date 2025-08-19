# Implementation Roadmap: Completing the ι-Generic Isometries

## Current Status
- ✅ Structure: Clean, ι-generic throughout  
- ✅ Patchlets: All critical fixes applied
- 🔄 Remaining: ~10 minor tactic errors + 17 mathematical `sorry` blocks

## Phase 1: Core CLM Construction (B3-B4)

### B3: `ofCoeffsCLM` - Build the functional
**Location**: Line 299
```lean
noncomputable def ofCoeffsCLM 
  (a : ι → ℝ) (ha : Summable (fun i => |a i|)) : c₀ →L[ℝ] ℝ
```

**Implementation Plan**:
1. Define the linear map: `toFun := fun x => ∑' i, a i * x i`
2. Prove linearity (map_add', map_smul')
3. Use `ContinuousLinearMap.mkContinuousOfExistsBound` with bound `∑' |a i|`
4. Key inequality: `‖a i * x i‖ ≤ |a i| * ‖x‖`

### B4: `ofCoeffsCLM_norm` - Norm equality
**Location**: Line 303
```lean
lemma ofCoeffsCLM_norm (a : ι → ℝ) (ha : Summable (fun n => |a n|)) :
  ‖ofCoeffsCLM a ha‖ = ∑' n, |a n|
```

**Implementation Plan**:
1. Upper bound (≤): Direct from mkContinuousOfExistsBound
2. Lower bound (≥): Test on sign vectors
   - Pick finite F with small tail
   - Define `x_F := ∑_{i∈F} sign(a i) • e i`
   - Show `‖x_F‖ ≤ 1` and `(ofCoeffsCLM a ha) x_F = ∑_{i∈F} |a i|`

## Phase 2: Truncation Convergence (B5)

### B5: `trunc_tendsto`
**Location**: Line 332
```lean
lemma trunc_tendsto (x : c₀) :
  Filter.Tendsto (fun F : Finset ι => trunc x F) Filter.atTop (𝓝 x)
```

**Implementation Plan**:
1. Use `Metric.tendsto_nhds` 
2. For ε > 0, find compact (hence finite) K where `‖x i‖ < ε` off K
3. Show that for F ⊇ K, `‖x - trunc x F‖ < ε`
4. Key: In discrete topology, compact = finite

## Phase 3: Isometry Infrastructure (B6-B10)

### B6: `toCoeffsL1` - Extract coefficients
**Location**: Line 339
```lean
noncomputable def toCoeffsL1 (f : c₀ →L[ℝ] ℝ) : lp (fun _ : ι => ℝ) 1
```
**Plan**: Package `i ↦ f(e i)` with summability from B1

### B7: `fromCoeffsL1` - Build from coefficients
**Location**: Line 343
```lean
noncomputable def fromCoeffsL1 (a : lp (fun _ : ι => ℝ) 1) : c₀ →L[ℝ] ℝ
```
**Plan**: Just `ofCoeffsCLM a.val (lp.summable_abs a)`

### B8-B9: Inverse lemmas
**Locations**: Lines 348, 353
- `fromCoeffsL1_toCoeffsL1`: Use CLM_ext_basis
- `toCoeffsL1_fromCoeffsL1`: Use finite support evaluation

### B10: `norm_toCoeffsL1`
**Location**: Line 358
**Plan**: Follows from B4 or use `dual_c0_iso_l1.norm_map`

## Phase 4: Supporting Lemmas (B1-B2)

### B1: `summable_abs_eval`
**Location**: Line 108
```lean
lemma summable_abs_eval (f : c₀ →L[ℝ] ℝ) : 
  Summable (fun n : ι => |f (e n)|)
```
**Plan**: Use approxSignVector machinery already in place

### B2: `finite_sum_bound`
**Location**: Line 114
```lean
lemma finite_sum_bound (f : c₀ →L[ℝ] ℝ) (s : Finset ι) :
  ∑ n ∈ s, ‖f (e n)‖ ≤ ‖f‖
```
**Plan**: Test on sign vector `∑_{i∈s} sign(f(e i)) • e i`

## Phase 5: Final Pieces (B11-B13)

### B11: Transport lemma
**Location**: Line 423
```lean
lemma DualIsBanach.congr {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] (e : X ≃ₗᵢ[ℝ] Y) :
  DualIsBanach X ↔ DualIsBanach Y
```

### B12-B13: WLPO theorems
**Locations**: Lines 433, 437
- Connect via the isometries to ℓ¹ and ℓ^∞

## Execution Order (Optimal Path)

1. **B3 → B4**: Core CLM construction (unlocks everything)
2. **B5**: Truncation (independent, can do anytime)
3. **B1 → B2**: Summability lemmas (needed for B6)
4. **B6 → B7**: Build to/from functions
5. **B8 → B9**: Prove inverses
6. **B10**: Norm preservation (trivial after B4)
7. **Fix LinearIsometryEquiv fields**: map_add', map_smul'
8. **B11 → B13**: Transport and WLPO (can do last)

## Tactic Fixes Still Needed

1. **Line 263**: Missing `{` in calc block
2. **Line 293**: `tsum_le_of_sum_le` type issue
3. **Line 327**: `trunc_apply` simp leaves goals
4. **Line 413**: CLM_ext_basis type mismatch

## Success Criteria
- [ ] All 17 `sorry` blocks replaced with proofs
- [ ] All compilation errors resolved
- [ ] File compiles cleanly with generic index ι
- [ ] Regression tests pass

## Notes
- Keep `classical` at top of sections using Finset/tsum
- Use `ha.tendsto_cofinite_zero` for tail estimates
- `tsum_subtype_eq_sum` bridges finite/infinite sums
- In discrete topology: `isCompact_iff_finite`