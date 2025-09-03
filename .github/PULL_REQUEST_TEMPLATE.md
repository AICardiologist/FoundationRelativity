## Description
<!-- Provide a brief description of the changes in this PR -->

## Type of Change
- [ ] Bug fix (non-breaking change which fixes an issue)
- [ ] New feature (non-breaking change which adds functionality)
- [ ] Breaking change (fix or feature that would cause existing functionality to not work as expected)
- [ ] Documentation update
- [ ] Refactoring

## Paper 3A/3B Guard
- [ ] 3A does not import ProofTheory
- [ ] 3B does not import 3A modules (Phase*, FT_Frontier, Examples)
- [ ] No `sorry`/`admit` outside `archive/`
- [ ] No `axiom` declarations in 3A
- [ ] Aggregators build (Paper3A_Main + Paper3B_Main)

## Testing
- [ ] Lake build passes locally
- [ ] Pre-commit hooks pass
- [ ] CI expected to pass

## Paper-Specific Checks
### If modifying Paper 1:
- [ ] Sherman-Morrison tests pass
- [ ] Sorries documented in README

### If modifying Paper 2:
- [ ] Bidual gap equivalence preserved
- [ ] Only 3 WLPO-conditional sorries remain

### If modifying Paper 3A:
- [ ] Framework remains axiom-free
- [ ] Examples compile without sorries
- [ ] HeightOracle pattern maintained

### If modifying Paper 3B:
- [ ] No new axioms added (frozen at 21)
- [ ] ProofTheory changes reviewed carefully
- [ ] Frozen markers preserved

## Additional Notes
<!-- Any additional information that reviewers should know -->