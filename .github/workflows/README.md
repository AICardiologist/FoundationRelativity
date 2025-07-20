# CI Workflows

This directory contains GitHub Actions workflows for continuous integration.

## Workflows

### `ci.yml` - Standard CI
- **Trigger**: On push to main and all PRs
- **Purpose**: Verify code builds and passes tests
- **Lean version**: Pinned to stable (4.3.0)
- **Tests**: Core tests that should always exist

### `nightly.yml` - Nightly CI
- **Trigger**: Daily at 2 AM UTC (or manual)
- **Purpose**: 
  - Test against Lean nightly builds
  - Detect breaking changes early
  - Automated dependency updates
- **Features**:
  - Builds with latest Lean nightly
  - Runs extended test suite
  - Creates automated PRs for mathlib bumps

## Environment Variables

- `LEAN_ABORT_ON_SORRY`: Set to 1 to ensure no `sorry` in proofs

## Adding New Tests

When adding new test executables:
1. Add to `lakefile.lean`
2. Update test list in `nightly.yml`
3. Consider adding to core tests in `ci.yml` if critical