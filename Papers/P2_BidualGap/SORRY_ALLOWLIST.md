# Paper 2 Sorry Allowlist

These are intentional, honest placeholders that mark missing mathematical content:

## Stub Lemmas (Constructive/Mathematical Content Missing)

1. **SORRY(P2-c0-witness)** in `Compat/NonReflexive.lean:37`
   - **Purpose**: Concrete witness construction via c₀ or ℓ¹ 
   - **TODO**: Use mathlib to prove ℓ¹(ℕ), c₀, or ℓ∞ is non-reflexive

2. **SORRY(P2-Ishihara-forward)** in `Constructive/Ishihara.lean:26`
   - **Purpose**: Ishihara's constructive encoding (BidualGap → WLPO)
   - **TODO**: Implement semi-decision procedure using gap element

3. **SORRY(P2-gap-implies-wlpo)** in `WLPO_Equiv_Gap.lean:21`
   - **Purpose**: Forward direction via Ishihara kernel
   - **TODO**: Wire Ishihara construction to main theorem

4. **SORRY(P2-wlpo-implies-gap)** in `WLPO_Equiv_Gap.lean:30`
   - **Purpose**: Reverse direction via c₀/ℓ∞ construction
   - **TODO**: Use WLPO to build non-representable functional

## Status

- **No hidden sorries**: All placeholders are explicit and marked
- **No vacuous proofs**: All current theorems are honest stubs
- **Ready for implementation**: Professor guidance will unlock genuine proofs

## CI Expectations

- Current: 4 expected `sorryAx` occurrences from marked stubs
- Target: 0 `sorryAx` after mathematical content implementation
- Failure condition: Any unmarked `sorry` or `sorryAx` not in this list