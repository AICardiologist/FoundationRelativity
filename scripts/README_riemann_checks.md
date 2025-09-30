# Riemann.lean Quality Gates

## Local Development

Run all checks:
```bash
./scripts/check.sh
```

Run individual checks:
```bash
./scripts/check-baseline.sh      # Verify 51-error baseline
./scripts/check-activation.sh     # Verify activation mode (default: baseline)
```

## CI Integration (Optional)

To add these checks to the Paper 5 workflow, insert after the Build Smoke step:

```yaml
      - name: Check Riemann activation mode
        run: ./scripts/check-activation.sh baseline
        continue-on-error: true  # Optional: make it informational

      - name: Check Riemann baseline (51 errors)
        run: ./scripts/check-baseline.sh
        continue-on-error: true  # Optional: make it informational
```

Note: The existing workflow has a "No sorries" check that expects zero sorries.
Since Riemann.lean intentionally has sorries (baseline 51 errors), these checks
should be separate or marked as informational.

## Activation Modes

When activating Stage-1 blocks, update the marker in Riemann.lean:
- `-- ACTIVATION_STATUS: baseline` (current)
- `-- ACTIVATION_STATUS: stage1-lhs-first`
- `-- ACTIVATION_STATUS: stage1-lhs-both`
- `-- ACTIVATION_STATUS: stage1-full`

Then update the check:
```bash
./scripts/check.sh stage1-lhs-first
```