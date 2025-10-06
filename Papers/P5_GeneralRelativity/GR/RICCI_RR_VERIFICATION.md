# Ricci R_rr = 0 Verification

## Professor's Sanity Check Formula

With:
- g^{tt} = -1/f
- g^{θθ} = 1/r²
- g^{φφ} = 1/(r²sin²θ)

And components:
- R_{trtr} = 2M/r³
- R_{θrθr} = -M/(r·f)
- R_{φrφr} = -M·sin²θ/(r·f)

Calculate:
```
R_rr = g^{tt} R_{trtr} + g^{θθ} R_{θrθr} + g^{φφ} R_{φrφr}
```

## Step-by-Step Calculation

**Term 1: g^{tt} R_{trtr}**
```
= (-1/f) · (2M/r³)
= -2M/(f·r³)
```

**Term 2: g^{θθ} R_{θrθr}**
```
= (1/r²) · (-M/(r·f))
= -M/(r³·f)
```

**Term 3: g^{φφ} R_{φrφr}**
```
= [1/(r²·sin²θ)] · [-M·sin²θ/(r·f)]
= -M/(r³·f)
```

**Sum:**
```
R_rr = -2M/(f·r³) - M/(r³·f) - M/(r³·f)
     = -2M/(f·r³) - 2M/(r³·f)
     = (-2M - 2M)/(f·r³)
     = -4M/(f·r³)
```

**ERROR!** This does NOT equal zero!

## What's Wrong?

The calculation shows R_rr = -4M/(f·r³) ≠ 0.

Possible issues:
1. The Ricci contraction formula is wrong
2. The component values are wrong
3. There are additional terms we're missing

## Check: Standard Schwarzschild R_rr Calculation

From Wald/Carroll, the Ricci tensor should contract as:

R_{ab} = R^c_{acb}

Not using the inverse metric! Let me check the actual contraction formula used in the code.

## Actual Riemann Contraction in Code

Looking at Papers/P5_GeneralRelativity/GR/Riemann.lean:

```lean
def RicciContraction (M r θ : ℝ) (a b : Idx) : ℝ :=
  sumIdx (fun ρ => gInv M r θ ρ ρ * Riemann M r θ ρ a ρ b)
```

This is: R_ab = g^{ρρ} R_{ρaρb}

**Wait!** This is summing over diagonal components only (ρ=ρ in gInv), not a full contraction!

This is actually:
```
R_ab = Σ_ρ g^{ρρ} R_{ρaρb}
```

For R_rr (a=r, b=r):
```
R_rr = g^{tt} R_{trtr} + g^{rr} R_{rrr r} + g^{θθ} R_{θrθr} + g^{φφ} R_{φrφr}
```

But R_{rrrr} = 0 by antisymmetry! So:
```
R_rr = g^{tt} R_{trtr} + g^{θθ} R_{θrθr} + g^{φφ} R_{φrφr}
```

This matches what we calculated above, which gives -4M/(f·r³), not zero!

## Hypothesis: Missing Component or Wrong Formula?

Let me check standard GR references for Schwarzschild R_{μν}.

Actually, the standard result is that **all** components of the Ricci tensor vanish for Schwarzschild!

So either:
1. Our component values are wrong
2. Our contraction formula is wrong
3. We're missing a component

## Alternative: Check if R_trtr sign is wrong

What if R_{trtr} should be negative?

Try: R_{trtr} = -2M/r³

Then:
```
R_rr = (-1/f)·(-2M/r³) + (1/r²)·(-M/(r·f)) + [1/(r²sin²θ)]·[-M·sin²θ/(r·f)]
     = 2M/(f·r³) - M/(r³·f) - M/(r³·f)
     = 2M/(f·r³) - 2M/(r³·f)
     = (2M - 2M)/(f·r³)
     = 0 ✓
```

**BINGO!** If R_{trtr} = -2M/r³, then R_rr = 0!

## Conclusion

The sign of R_{trtr} may also need to be corrected!

Current code has:
```lean
lemma R_rtrt_eq (M r θ : ℝ) (hM : 0 < M) (h_r_gt_2M : 2 * M < r) :
  Riemann M r θ Idx.r Idx.t Idx.r Idx.t = (2 * M) / r^3 := by
```

Should be:
```lean
Riemann M r θ Idx.r Idx.t Idx.r Idx.t = -(2 * M) / r^3
```

Similarly, by symmetry, R_trtr should also be negative.

## Verification Needed

Check the professor's message again - did they mention R_{trtr} needing a sign correction too?
