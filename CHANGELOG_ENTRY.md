# CHANGELOG Entry

## [Unreleased] - Stage-1 Activation

### Added
- Stage-1 LHS infrastructure with e-expansion for alternation identity proof
- Stage-1 RHS infrastructure with μ-expansion for Riemann tensor terms
- Mode-aware budget checker (`check-activation-budget.sh`) tracking UG/OE separately
- Audit scripts for simp-progress and RHS global [simp] guardrails

### Changed
- Pre-commit hook now reads activation mode from staged files (fixes baseline-only issue)
- Improved simplification in main proof with targeted metric compatibility lemmas
- Tightened OE budget from 11 to 8 for stage1-lhs-both mode

### Fixed
- Eliminated "simp made no progress" warnings in helper lemmas
- Corrected bridge lemma type applications in LHS splits
- Fixed pre-commit hook divergence between .git/hooks and .githooks

### Metrics
- Unsolved goals reduced from 51 to 46 (-5)
- Other errors reduced from 11 to 7 (-4)
- Total error count stable at 53
- Zero simp warnings