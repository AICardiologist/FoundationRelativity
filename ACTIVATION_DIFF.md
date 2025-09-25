# Stage-1 LHS+RHS Activation Diff Summary

## Key Changes in Riemann.lean

### Added Sections (File-scope)
- **Stage1_LHS_Splits** (lines 1070-1145): LHS e-expansion with bridge lemmas
- **Stage1_RHS_Splits** (lines 1147-1207): RHS μ-expansion infrastructure

### Main Proof Wiring (alternation_dC_eq_Riem)
- **Lines 1240-1245**: Wire LHS splits via Hsplit_c_both/Hsplit_d_both
- **Lines 1248-1254**: Apply 4-term linearity to all split components
- **Lines 1256-1450**: Product rule pushes for all 16 summands
- **Lines 1489-1494**: Wire RHS splits via Hsplit_RHS_combined

### Simplification Changes
- **Lines 579, 597**: Changed `simp only` to `simp` in helper lemmas
- **Lines 1485-1487**: Added targeted simp_all with metric compatibility
- **Line 1210**: Added dCoord_zero_fun helper

## Infrastructure Changes

### Scripts Added
- `scripts/check-activation-budget.sh`: Mode-aware UG/OE tracking
- `scripts/audit-simp-progress.sh`: Guard against simp warnings
- `scripts/audit-rhs-splits.sh`: Guard against global [simp] on RHS

### Hook Fixes
- `.githooks/pre-commit`: Now reads staged activation mode (was hardcoded baseline)
- Added CR-safe trimming and working tree fallback

### Makefile Updates
- Added new audits to `make audit` target

## Metrics Impact

| Metric | Baseline | After LHS | After RHS | Change |
|--------|----------|-----------|-----------|---------|
| UG     | 51       | 46        | 46        | **-5**  |
| OE     | 2        | 11        | 7         | **+5**  |
| Total  | 53       | 57        | 53        | **0**   |
| Simp warnings | 0 | 2      | 0         | **0**   |

## Activation Status
```lean
-- ACTIVATION_STATUS: stage1-lhs-both
```

## Files Changed
- Papers/P5_GeneralRelativity/GR/Riemann.lean (+438, -7)
- .githooks/pre-commit (+23, -4)
- Makefile (+2, -1)
- scripts/* (5 files added/modified)