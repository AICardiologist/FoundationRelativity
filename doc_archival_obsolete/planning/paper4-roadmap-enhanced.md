# Paper 4 Enhanced Roadmap: Fast-Track Discrete Approach

## Current Status

- **Papers 1-3**: 0 sorries (100% complete!)
- **Paper 4**: 28 sorries (axiomatized neck scaling + discrete CPW model infrastructure)

## Two-Track Strategy

### Track A: Fast Track (6-7 weeks) - Discrete CPW Model
**Goal**: Prove undecidability using discrete graph approximation

### Track B: Long Term (24-36 months) - Full Smooth Geometry
**Goal**: Complete smooth manifold implementation

## Fast Track Implementation Plan

### Phase 1A: Discrete CPW Infrastructure ✅ COMPLETE
- Created discrete neck torus graph structure
- Defined discrete Laplacian operator  
- Implemented Turing machine encoding framework
- Set up interval bookkeeping for spectral bands
- Showed spectral condition is Π₁

**Status**: All modules compiling with 28 documented sorries

### Phase 1B: Core Lemmas (Week 1-2) ⬅️ NEXT
**Goal**: Prove key supporting lemmas

1. **Spectral Band Properties** (3-4 days)
   - Complete `unperturbed_bands_disjoint` proof
   - Prove band ordering lemmas
   - Show perturbations stay within bands

2. **Harmonic Series Bounds** (2-3 days)
   - Prove `maxPerturbation` bounds
   - Show convergence for halting TMs
   - Show divergence for non-halting TMs

3. **Rayleigh Quotient Properties** (2-3 days)
   - Prove `orthogonal_is_primrec`
   - Prove `rayleigh_is_primrec`
   - Complete Π₁ encoding proofs

### Phase 1C: Main Undecidability Theorem (Week 3-4)
**Goal**: Prove `spectral_gap_jump` theorem

1. **Forward Direction** (3-4 days)
   - If TM halts → spectral gap stays large
   - Use `halting_preserves_gap` lemma
   - Show perturbations bounded by harmonic sum

2. **Reverse Direction** (3-4 days)
   - If TM doesn't halt → spectral gap shrinks
   - Use `non_halting_kills_gap` lemma
   - Show unbounded perturbation accumulation

3. **Threshold Behavior** (2-3 days)
   - Prove `threshold_dichotomy`
   - Show clear separation at rational threshold
   - Connect to consistency predicate

### Phase 1D: Documentation & Testing (Week 5-6)
**Goal**: Complete fast-track implementation

1. **Code Documentation** (2-3 days)
   - Add detailed proofs documentation
   - Create usage examples
   - Write mathematical exposition

2. **Test Suite** (2-3 days)
   - Add regression tests
   - Create concrete examples
   - Verify threshold calculations

3. **Integration** (2-3 days)
   - Update main README
   - Create PR with full implementation
   - Run comprehensive testing

### Phase 1E: Polish & Publication (Week 7)
**Goal**: Prepare for release

1. **Final Review**
   - Code review all proofs
   - Verify sorry count unchanged
   - Check CI compliance

2. **Documentation Updates**
   - Update paper LaTeX with discrete results
   - Add implementation notes
   - Create blog post/announcement

## Detailed Next Steps

### Immediate Actions (Today)
1. Start proving spectral band lemmas in `IntervalBookkeeping.lean`
2. Focus on arithmetic properties needed for `unperturbed_bands_disjoint`
3. Set up helper lemmas for rational arithmetic

### Week 1 Goals
- Complete all IntervalBookkeeping proofs (reduce from 7 to 0-2 sorries)
- Prove basic properties in Pi1Encoding (reduce from 7 to 3-4 sorries)
- Start on TuringEncoding helper lemmas

### Success Metrics
- Reduce total Paper 4 sorries from 28 to ~10-12
- Have spectral_gap_jump theorem statement verified
- All discrete modules building without errors

## Long-Term Vision (Track B)

### Year 1: Infrastructure
- Implement smooth manifolds in Lean 4
- Add Riemannian geometry basics
- Create spectral theory framework

### Year 2: Construction
- Implement Cheeger neck metrics
- Add smooth bump functions
- Prove smooth version of theorems

### Year 3: Integration
- Connect discrete and smooth approaches
- Prove approximation theorems
- Complete full Paper 4 vision

## Risk Mitigation

### Technical Risks
1. **Arithmetic complexity**: Use `ring_nf` and `field_simp` tactics
2. **Proof size**: Break into smaller lemmas
3. **Performance**: Use `noncomputable` where needed

### Schedule Risks
1. **Blocked on proofs**: Move to next module, return later
2. **Unexpected complexity**: Simplify construction further
3. **Time overrun**: Focus on core theorem, leave polish for later

## Conclusion

The fast-track approach provides a pragmatic path to completing Paper 4's core mathematical content in 6-7 weeks, while leaving the door open for the full smooth geometry implementation in the future. With Papers 1-3 complete, this discrete approach will give us a fully formalized Foundation-Relativity hierarchy.