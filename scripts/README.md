# Foundation-Relativity Scripts

This directory contains scripts and tools for maintaining code quality and enforcing formalization standards.

## QA-Mandated No-Shortcuts Tools

These tools were created in response to QA findings that the repository was using Unit/() tricks to achieve "0 sorries" without real formalization.

### 🔍 `lean/CheapProofs.lean`
**Purpose**: Detect theorems that use only trivial proofs without real mathematical content.

**Usage**: 
```bash
lake exe cheap_proofs
```

**What it catches**:
- Theorems proved with `exact ⟨()⟩`
- Proofs using only `Init.*`, `Unit`, `True`, `trivial`
- Any theorem that doesn't reference real mathematical definitions

**Exit codes**:
- 0: No cheap proofs found
- 1: Cheap proofs detected

### 🔲 `check_struct_stubs.py`
**Purpose**: Detect Unit stub structures and trivial Prop definitions.

**Usage**:
```bash
python scripts/check_struct_stubs.py
```

**What it catches**:
- `structure X where dummy : Unit`
- `def X : Prop := True`
- `abbrev X := Unit`
- Vacuous proofs like `by trivial` for non-trivial claims

**Exit codes**:
- 0: No stubs found
- 1: Stubs detected

### 📊 `check_alignment.py`
**Purpose**: Verify that LaTeX theorems are properly formalized in Lean.

**Usage**:
```bash
python scripts/check_alignment.py
```

**What it does**:
1. Extracts all theorems from LaTeX papers
2. Searches for corresponding Lean declarations
3. Verifies proofs use real mathematical content
4. Generates alignment report

**Output**:
- Console summary
- `alignment_report.json` with detailed results

**Exit codes**:
- 0: All theorems properly aligned
- 1: Missing or suspicious theorems found

## Other Scripts

### `verify-no-sorry.sh`
Verifies that no `sorry` remains in the codebase (except in allowed test files).

### `check-no-axioms.sh`
Ensures no unauthorized axioms are introduced outside of designated axiom files.

### `regression-test.sh`
Comprehensive test suite that runs all paper smoke tests and verifies the build.

## CI Integration

All no-shortcuts tools are integrated into CI:
- Main workflow (`.github/workflows/ci.yml`)
- Dedicated no-shortcuts workflow (`.github/workflows/no-shortcuts.yml`)

PRs will fail if any of these checks detect violations.

## Golden Rules

1. **Only two states for theorems**: Contains `sorry` OR has real proof
2. **No Unit stubs**: Use real definitions or `sorry`
3. **No trivial-only proofs**: Must use mathematical content
4. **Cross-reference LaTeX**: Include `-- (LaTeX Theorem X.Y)` comments

## Exceptions

See [docs/no-shortcuts-exceptions.md](../docs/no-shortcuts-exceptions.md) for handling legitimate short proofs.

## Contributing

When adding new scripts:
1. Document purpose and usage clearly
2. Include exit codes
3. Add to appropriate CI workflows
4. Update this README
