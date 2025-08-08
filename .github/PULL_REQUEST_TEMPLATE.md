# Paper 3 Framework PR Checklist

## Summary
<!-- Brief description of changes -->

## Pre-submission Requirements

### Build & Tests
- [ ] Builds locally with `lake build Papers.P3_2CatFramework.Basic`
- [ ] `./scripts/guard_vacuity.sh` passes
- [ ] CI tests compile:
  - [ ] `Papers/P3_2CatFramework/test/Interp_simp_test.lean`  
  - [ ] `Papers/P3_2CatFramework/test/TwoCell_simp_test.lean`

### Code Quality
- [ ] No new `sorry`/`admit` outside whitelist:
  - ✅ Allowed: `Papers/P3_2CatFramework/Blueprint/`
  - ✅ Allowed: `Papers/P3_2CatFramework/FunctorialObstruction.lean`
  - ❌ Not allowed: Core framework files
- [ ] No vacuous implications (e.g., `AssocHolds → ...`) in code (docs excluded)
- [ ] All placeholders remain non-trivial (empty inductives, no constructors)

### Framework Integrity  
- [ ] `TwoCell` orientation is `φ.map_obj x = ψ.map_obj x` (source = target)
- [ ] Scoped notation hints present in both:
  - [ ] `Papers/P3_2CatFramework/Core/Coherence.lean`
  - [ ] `Papers/P3_2CatFramework/Core/Prelude.lean`
- [ ] Exported simp lemmas use collision-safe names (`id_vcomp`, `vcomp_id`, `vcomp_assoc`)
- [ ] @[simp] lemmas for TwoCell operations are definitional (`:= rfl`)

### Documentation
- [ ] Changes align with Paper 3 non-vacuous placeholder principles
- [ ] Any new framework components documented in commit message
- [ ] Blueprint files clearly marked as development/experimental

## Testing Notes
<!-- Describe any manual testing performed -->

## Related Issues
<!-- Link to relevant GitHub issues -->

---
*This PR contributes to the Paper 3: 2-Categorical Framework implementation. All items must be checked before merge.*