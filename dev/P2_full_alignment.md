# Paper 2 — Full Alignment Notes (for local dev only)

This note lists what to check/update when you align mathlib and the toolchain to work on the "full" HB side.

## Targets

- **CI target** (unchanged): `Papers.P2_BidualGap.P2_Minimal` — stays dependency-free and sorry-free.
- **Local smoke target**: `Papers/P2_BidualGap/P2_Smoke.lean` — only `#check`s; fast indicator of name drift.

## Toolchain checklist

1. Ensure Lean version matches mathlib's:
   - Check `.lake/packages/mathlib/lean-toolchain`
   - Align project `lean-toolchain` accordingly, then:
     ```bash
     lake update
     lake clean
     find . -name "*.olean" -delete
     ```

2. Warm cache (optional):
   ```bash
   lake exe cache get || true
   ```

3. Smoke-test names:
   ```bash
   lake env lean Papers/P2_BidualGap/P2_Smoke.lean
   ```
   - If this fails, update imports/signatures as indicated by Lean's messages.

## HB/Constructive modules & common imports

- **Completeness shim** (version-stable):
  - `Papers/P2_BidualGap/HB/Compat/CompletenessTransport.lean`
  - Imports: `Mathlib.Topology.UniformSpace.Basic`,
    `Mathlib.Topology.Algebra.UniformGroup`,
    `Mathlib.Topology.Algebra.Module`

- **OpNormCore** (minimal):
  - `Papers/P2_BidualGap/Constructive/OpNormCore.lean`
  - Imports: `Mathlib.Analysis.NormedSpace.OperatorNorm`

- **Dual isometries** (heavy):
  - `Papers/P2_BidualGap/HB/DualIsometriesComplete.lean`
  - Typical deps: `Mathlib.Analysis.Normed.Group.InfiniteSum`,
    `Mathlib.Topology.Algebra.InfiniteSum.Basic`,
    `Mathlib.Topology.Algebra.InfiniteSum.ENNReal`,
    `Mathlib.Data.Real.Basic`

## Known API drift points & how we neutralized them

- **Completeness transport across ≃ₗᵢ**: replaced with our shim
  `HB.Compat.completeSpace_of_linearIsometryEquiv`, which uses only uniform continuity and Cauchy filters.

- **Operator-norm heaviness**: Ishihara now uses `Constructive/OpNormCore.lean`, a Prop-level interface
  (`UnitBall`, `valueSet`, `HasOpNorm`, zero-functional facts) to avoid fragile csSup/tsum flows.

## When the smoke passes

- Uncomment and build non-CI local aggregators (e.g. `P2_Full.lean`) and iterate on the HB side.
- Keep CI pinned to `P2_Minimal` only.

---

## Key mathlib surfaces we depend on

### Core functional analysis
- `NormedAddCommGroup`, `NormedSpace` — basic normed space structure
- `ContinuousLinearMap` — bounded operators `X →L[ℝ] ℝ`
- `LinearIsometryEquiv` — isometric isomorphisms

### Sequence spaces
- `lp` — ℓᵖ spaces
- `ZeroAtInfty` — c₀ space
- `BoundedContinuousFunction` — ℓ∞ space

### Topology/Completeness
- `CompleteSpace`, `Cauchy` — completeness via Cauchy filters
- `UniformContinuous` — uniform continuity
- `Filter.map`, `Filter.tendsto` — filter operations

### Real analysis
- `abs`, norm operations
- `HasSum`, `tsum` — infinite sums (when needed)

---

## Troubleshooting common issues

1. **"object file does not exist"**: Toolchain mismatch. Follow toolchain checklist above.

2. **API name changes**: Run smoke target to identify which names moved, then update imports.

3. **Signature changes**: Check mathlib docs for the new signature, adjust type annotations.

4. **Missing imports**: Use `lake exe graph` to trace dependencies.

---

## Quick validation after alignment

```bash
# 1. Minimal target (should always work)
lake build Papers.P2_BidualGap.P2_Minimal
./scripts/no_sorry_p2_minimal.sh

# 2. Smoke target (after toolchain alignment)
lake env lean Papers/P2_BidualGap/P2_Smoke.lean

# 3. Full build (when ready to work on HB)
lake build Papers.P2_BidualGap.P2_Full
```