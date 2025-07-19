# PR Creation Templates

Use these exact titles and descriptions when creating the PRs on GitHub.

---

## PR-1: feat/witness-core → main

**Title:** `Sprint S2: Implement unified witness API (feat/witness-core)`

**Description:**
```markdown
## Summary
Introduces `Found.WitnessCore` with generic `WitnessType` and `pathologyFunctor` to replace hand-rolled Empty/PUnit patterns across pathology functors.

## Changes
- ✨ Add `Found.WitnessCore` with:
  - `WitnessType`: generic witness function `(α : Type) → Foundation → Type`
  - `pathologyFunctor`: builds covariant `Foundation ⥤ Cat` from any type α
- 🧪 Add `WitnessTests` executable for API validation
- 🔧 Update CI to include witness tests
- 📝 Add no-sorry verification script

## Testing
- All existing tests pass
- New `WitnessTests` validates the API
- `LEAN_ABORT_ON_SORRY=1` verification succeeds

This establishes the foundation for Sprint S3 pathology migrations.

**Sprint S2 Milestone**: Infrastructure complete for formal proof development.
```

**Link:** https://github.com/AICardiologist/FoundationRelativity/pull/new/feat/witness-core

---

## PR-2: feat/gap2-witness-api → main

**Title:** `PR-2: Migrate Gap₂ to WitnessCore API`

**Description:**
```markdown
## Summary
Refactors Gap₂ to use the new unified witness API from `Found.WitnessCore`.

## Changes
- ♻️ Replace hand-rolled Empty/PUnit pattern with `pathologyFunctor`
- 🗑️ Remove redundant `Gap2/Witness.lean`
- ✨ Add `Gap₂Pathology` type for type-safe witness function
- 🧪 Add `Gap2MigrationTest` to validate the migration
- 🔧 Update CI to include migration test

## Testing
- All tests pass
- `Gap₂` now demonstrates the simplified API pattern for future migrations
- Verified: `Gap.Gap₂ = pathologyFunctor Gap.Gap₂Pathology`

## Dependencies
Depends on: #1 (feat/witness-core)
```

**Link:** https://github.com/AICardiologist/FoundationRelativity/pull/new/feat/gap2-witness-api

---

## PR-3: feat/ap-rnp-witness-api → main

**Title:** `PR-3: Migrate all pathology functors to WitnessCore API`

**Description:**
```markdown
## Summary
Complete migration of all three pathology functors to use the unified witness API.

## Changes
- ♻️ Migrate all functors to use `pathologyFunctor`:
  - `Gap₂`: Uses `Gap₂Pathology` type
  - `AP_Fail₂`: Uses `APPathology` type
  - `RNP_Fail₂`: Uses `RNPPathology` type
- 🗑️ Remove all redundant `Witness.lean` files
- 🧪 Add comprehensive `AllPathologiesTest`
- 🔧 Update `NonIdMorphisms` test for new API behavior

## Testing
- All tests pass
- Verified all functors equal their `pathologyFunctor` construction
- Code reduction: ~60% less boilerplate

The codebase now consistently uses the simplified witness API pattern.

## Dependencies
Depends on: #2 (feat/gap2-witness-api)
```

**Link:** https://github.com/AICardiologist/FoundationRelativity/pull/new/feat/ap-rnp-witness-api

---

## PR-4: feat/nightly-ci → main

**Title:** `PR-4: Add CI/CD workflows`

**Description:**
```markdown
## Summary
Implement comprehensive CI/CD setup with standard and nightly workflows.

## Features

### Standard CI (`ci.yml`)
- 🔧 Runs on all PRs and pushes to main
- 📌 Uses pinned Lean 4.3.0 for stability
- ✅ Runs core test suite
- 🚫 Verifies no 'sorry' in proofs

### Nightly CI (`nightly.yml`)
- 🌙 Runs daily at 2 AM UTC
- 🔬 Tests against Lean nightly builds
- 🚨 Detects breaking changes early
- 🤖 Automated mathlib dependency bumps
- 📬 Creates PRs for successful updates

### Infrastructure
- ✅ `verify-no-sorry.sh` script
- 📚 CI workflow documentation
- 🏷️ README with status badges

This establishes a robust testing pipeline to maintain code quality and stay current with Lean ecosystem updates.

## Dependencies
Depends on: #3 (feat/ap-rnp-witness-api)

**Sprint S2 Complete**: Ready for formal proof development in Sprint S3.
```

**Link:** https://github.com/AICardiologist/FoundationRelativity/pull/new/feat/nightly-ci

---

## Quick Creation Checklist

1. ✅ Click each link above
2. ✅ Copy-paste the exact title and description
3. ✅ Ensure base branch is `main`
4. ✅ Add dependency notes for PR-2, PR-3, PR-4
5. ✅ Create PR
6. ✅ Repeat for all 4 PRs

## After All PRs Created

Merge in order: **PR-1 → PR-2 → PR-3 → PR-4**

Then tag the release:
```bash
git checkout main && git pull origin main
git tag -a v0.3.0-witness -m "Sprint S2: Witness API + migrations complete"
git push origin v0.3.0-witness
```

This marks Sprint S2 completion and unblocks Sprint S3 formal proof development!