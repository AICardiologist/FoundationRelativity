# Paper 2 – Honest stubs in place for WLPO ↔ BidualGap

## Summary

We have replaced our earlier placeholder code with clean stubs that accurately reflect the missing mathematics in both directions of the equivalence.

- The forward direction (BidualGap → WLPO) is structured via a new `Constructive.Ishihara` skeleton, to follow Ishihara's argument (Option A).
- The reverse direction (WLPO → BidualGap) is stubbed to follow the c₀/ℓ∞ route (Option B).  
- The compatibility layer now only declares the existence proposition `NonReflexiveWitness ℝ` and a repackaging lemma; there are no misleading instances.

We replaced the prior typeclass/instance pattern with a neutral `NonReflexiveWitness ℝ : Prop` plus a small repackaging lemma; there is no global instance, so the reverse direction **must** explicitly use WLPO (or your chosen HB fragment) to produce a witness—there's no ambient proof hiding in the environment.

## Current File Structure

1. **`Basic.lean`** - Minimal definitions of `BidualGap` and `WLPO`
2. **`Compat/NonReflexive.lean`** - Witness existence proposition with stub `c0_or_l1_witness`
3. **`Constructive/Ishihara.lean`** - Forward direction skeleton with `IshiharaKernel` and `encode` 
4. **`WLPO_Equiv_Gap.lean`** - Main equivalence bundling both stub directions
5. **`test/Axioms.lean`** - Honest axiom checking (shows `sorryAx` from stubs)

## Ready for Implementation

We're ready to fill in the constructive `encode`/evaluation mechanism and the c₀ functional construction. If you'd like us to prioritize one direction first (e.g., forward Ishihara), we'll implement that next.

### Questions for Implementation Guidance

**1. Forward Direction (BidualGap → WLPO) - Ishihara's Argument:**

Could you point us to the exact statement/reference for extracting the encoding kernel from a gap element `y ∈ X** \ j(X)`? We have structured it as:

```lean
structure IshiharaKernel : Type :=
  (j : X →L[ℝ] (NormedSpace.Dual ℝ (NormedSpace.Dual ℝ X)))
  (not_surj : ¬ Function.Surjective j)

def encode (K : IshiharaKernel) (α : ℕ → Bool) : X := 
  -- Will be: ∑' n, (encode_weight α n) • K.x n
```

We plan the semi-decision property: for any `α`, either `|y(encode α)| = 0` or `|y(encode α)| ≥ δ` based on whether `∀ n, α n = false`.

**2. Reverse Direction (WLPO → BidualGap) - c₀/ℓ∞ Route:**

For the c₀ construction, should we:
- Prove `WLPO → HB_Fragment` in our code (with your recommended reference), or 
- May we cite the WLPO ≡ Hahn-Banach equivalence and focus our proof effort on `HB_Fragment → BidualGap`?

We're planning to work with `X := c₀(ℕ, ℝ)` with `X* = ℓ¹` and `X** = ℓ∞`, using WLPO to construct a functional that vanishes on `c₀` but isn't in the `ℓ¹` representation.

## Engineering Status

- **No global instances with sorry** - prevents accidental fake proofs
- **4 tracked `sorry` placeholders** - added to CI allowlist  
- **Classical logic confined** - only in main equivalence file, not in constructive kernel
- **Axiom hygiene testing** - will show clean status when stubs are filled

Thanks—once we fix these two implementation choices, we can deliver a fully honest equivalence.