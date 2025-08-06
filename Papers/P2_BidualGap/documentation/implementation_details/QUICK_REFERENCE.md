# Paper 2 Quick Reference Guide

## File Structure

```
Papers/P2_BidualGap/
├── Constructive/           # All constructive mathematics
│   ├── CReal.lean         # Constructive reals (Cauchy + modulus)
│   ├── NormedSpace.lean   # CNormedSpace without classical axioms
│   ├── Sequences.lean     # ℓ∞ and c₀ spaces
│   ├── MonotoneConvergence.lean  # Key convergence theorem
│   ├── WLPO_ASP_Core.lean       # The bridge: WLPO ↔ ASP
│   ├── HahnBanach.lean          # Constructive extension theorem
│   └── MainTheoremFinal.lean    # Bidual Gap ↔ WLPO
├── Logic/
│   └── WLPOSimple.lean    # Basic WLPO definition
└── Analysis/              # (Old classical approach - deprecated)

```

## Key Definitions

### Constructive Real (CReal)
```lean
structure CReal where
  seq : ℕ → ℚ      -- Cauchy sequence
  mod : ℕ → ℕ      -- Modulus of convergence
  is_cauchy : ...   -- Explicit rate
```

### WLPO (Weak Limited Principle of Omniscience)
```lean
def WLPO : Prop :=
  ∀ α : ℕ → Bool, (∀ n, α n = false) ∨ ¬(∀ n, α n = false)
```

### ASP (Approximate Supremum Property)
```lean
def ASP : Prop :=
  ∀ S : CountableSet, ∀ ε > 0, ∃ x, isApproxSup S ε x
```

### Located Subspace
```lean
structure Located (E : Type*) [CNormedSpace E] (S : Set E) where
  dist : E → CReal
  dist_property : ...  -- Can compute distance to S
```

## Key Theorems

1. **WLPO ↔ ASP** (WLPO_ASP_Core.lean)
   - Uses gap encoding and rational comparisons
   - Avoids undecidable CReal ordering

2. **c₀ is located in ℓ∞** (Sequences.lean)
   - Via limsup and monotone convergence
   - NOT via decidable membership

3. **Constructive Hahn-Banach** (HahnBanach.lean)
   - Requires ASP for extension values
   - Works for located subspaces only

4. **Bidual Gap ↔ WLPO** (MainTheoremFinal.lean)
   - Gap → WLPO: witness sequence method
   - WLPO → Gap: ASP → HB → Banach limit

## Critical Principles to Remember

### DO NOT:
- Import `Classical` anything
- Assume decidable equality/ordering on CReal
- Use uncountable sets without enumeration
- Assume suprema exist without ASP

### DO:
- Work with rational approximations
- Use monotone convergence for existence
- Keep sets countable with explicit enumerations
- Mark incomplete proofs with `sorry` not tricks

## Common Patterns

### Rational Approximation
```lean
def approx_at (x : CReal) (n : ℕ) : ℚ := x.seq (x.mod n)
```

### Decidable Rational Comparison
```lean
by_cases h : (q : ℚ) < 1/4  -- OK: decidable
by_cases h : x < y           -- NOT OK if x, y : CReal
```

### Countable Set Encoding
```lean
structure CountableSet where
  seq : ℕ → ℚ
  bounded : ∃ B, ∀ n, |seq n| ≤ B
```

## Debugging Tips

1. **"No instance for Decidable"**: You're comparing CReals. Use rational approximations.

2. **"Classical.em required"**: You're using classical logic. Find the constructive workaround.

3. **"Type mismatch CReal vs ℚ"**: Use `from_rat` to embed rationals.

4. **Proof won't close**: Check if you need ASP/WLPO hypothesis.

## Next Steps for Completion

1. Fix Lean syntax in WLPO_ASP files
2. Complete CReal arithmetic (multiplication, abs)
3. Fill in binary search convergence proof
4. Run lake build and fix type errors
5. Add to CI pipeline with no-classical check