# Paper 3C: DCω → Baire Calibrator

The third orthogonal axis of the Axiom Calibration (AxCal) framework.

## Structure

```
P3C_DCwAxis/
├── DCw_Frontier_Interface.lean   # DCω definition + opaque BaireNN token
├── DCw_Skeleton.lean             # Complete proof (0 sorries)
├── DCw_Baire.lean               # Main theorem (1 intentional sorry)
├── DCw_TopBinding_Complete.lean # Adapter stub (awaiting mathlib)
├── DCw_Complete.lean            # Semantic proof outline
├── DCw_TopBinding.lean.future   # Ready-to-paste adapter
└── DCw_Baire_Complete.lean.future # Ready-to-paste final theorem
```

## Build Instructions

### Core (always green)
```bash
lake build Papers.P3C_DCwAxis.DCw_Skeleton Papers.P3C_DCwAxis.DCw_Baire
```

### With binding stubs
```bash
lake build Papers.P3C_DCwAxis
```

## Mathematical Content

### Proven (0 sorries)
- **`chain_of_DCω`**: Given DCω and countable DenseOpen family, builds indexed chain
- **`limit_mem`**: Diagonal limit belongs to every cylinder in the chain
- **Helper lemmas**: Length monotonicity, prefix stability, digit extraction

### Key Innovation
Stage-indexed refinement ensures hitting U_n at stage n specifically, enabling clean diagonal construction.

## Completing the Binding

When mathlib topology is available:

1. Replace stub with adapter:
```bash
cp DCw_TopBinding.lean.future DCw_TopBinding.lean
```

2. Replace theorem with complete version:
```bash
cp DCw_Baire_Complete.lean.future DCw_Baire.lean
# (or just replace the theorem body)
```

3. Build complete axis:
```bash
lake build Papers.P3C_DCwAxis
```

Expected: 0 sorries.

## Paper Integration

This establishes the third calibrator axis:
- **Paper 3A**: BI → WKL (Lindenbaum)
- **Paper 3B**: Con(PA) → RFN(Σ₁) (Gödel)  
- **Paper 3C**: DCω → Baire (Dependent Choice)

All three axes are orthogonal, demonstrating distinct calibration pathways.
