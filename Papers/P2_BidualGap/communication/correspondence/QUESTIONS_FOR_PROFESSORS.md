# Questions for Professors - Paper 2

## For Junior Professor

Thank you for your detailed guidance on the constructive implementation. We have made progress implementing your suggestions:

1. **Monotone Modulus**: Implemented `Modulus.mono` as suggested
2. **Rational Arithmetic**: Added `partial_sum` helper and started simplifying witness sequence proof
3. **Gap Encoding**: Using the 0 vs ≥1/2 approach to avoid CReal comparisons

### Current Blockers

1. **CReal Import Issues**: 
   - Cannot find `Mathlib.Data.Rat.Order` 
   - Need correct import for rational ordering lemmas
   - Should we use a different Mathlib module?

2. **Witness Sequence Convergence**:
   - Working on the contradiction in `witness_in_c_zero_iff`
   - The CReal comparison `lt` is making the proof complex
   - Should we lift everything to rational comparisons first?

3. **Located Distance**:
   - For `c_zero_located`, need to show distance property
   - How to handle the limsup construction constructively?

### Implementation Question

Given that we're hitting complexity with CReal comparisons, would it be better to:
- Work entirely in ℚ and only lift to CReal at the end?
- Or maintain CReal throughout but add more comparison lemmas?

## For Senior Professor

We are implementing the genuine constructive framework as you advised. The Unit/() tricks have been completely removed. 

### Strategic Question

The constructive proof is significantly more complex than anticipated. Given our timeline constraints, should we:
1. Continue with the full constructive implementation (currently 55 sorries)
2. Document the constructive approach thoroughly but focus on getting key results?
3. Prioritize which parts are most important for the paper's contribution?

## Progress Summary

- Removed all Unit/() cheats
- Main theorem statement compiles with honest sorries
- Constructive framework ~70% complete
- Following junior professor's blueprint closely

## Next Steps

Awaiting your guidance on:
1. Import path corrections for Mathlib
2. Simplification strategy for CReal proofs
3. Priority for remaining constructive components