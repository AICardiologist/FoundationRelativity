# Stone Window API Documentation

**Status**: Production-ready API with 100+ lemmas  
**Module**: `Papers.P3_2CatFramework.P4_Meta.StoneWindow_SupportIdeals`

**Certification Note**: Constructive surjectivity is fully certified for the finite support ideal. Non-metric ideals are handled as calibration targets; the API supports reasoning on both sides uniformly, but CI only certifies finite support constructively.

## Overview

The Stone Window provides a complete Boolean algebra API for idempotents in ℓ∞/c₀, with extensive simp automation and a calibration framework for surjectivity results.

## Core Types

### SupportIdeal
```lean
structure SupportIdeal where
  carrier : Set (Set ℕ)
  finite_union : ∀ {A B}, A ∈ carrier → B ∈ carrier → A ∪ B ∈ carrier
  subset_closed : ∀ {A B}, A ⊆ B → B ∈ carrier → A ∈ carrier
```

### Idempotent Elements
```lean
def Idem (𝓘 : SupportIdeal) := {e : ℝ^ℕ | e * e = e ∧ SupportIn 𝓘 e}
```

## Boolean Algebra Operations (100+ lemmas)

### Basic Operations
- `idemBot` - Bottom element (0)
- `idemTop` - Top element (1)  
- `idemSup` - Join (∨)
- `idemInf` - Meet (∧)
- `idemCompl` - Complement (¬)
- `idemDiff` - Difference (a \ b)
- `idemXor` - Symmetric difference (a ⊕ b)

### Key Simp Lemmas

#### Idempotent Laws
```lean
@[simp] lemma idemSup_idem : idemSup 𝓘 e e = e
@[simp] lemma idemInf_idem : idemInf 𝓘 e e = e
```

#### Absorption Laws
```lean
@[simp] lemma idemSup_inf_absorb : idemSup 𝓘 e (idemInf 𝓘 e f) = e
@[simp] lemma idemInf_sup_absorb : idemInf 𝓘 e (idemSup 𝓘 e f) = e
```

#### Complement Laws
```lean
@[simp] lemma idemSup_compl_eq_top : idemSup 𝓘 e (idemCompl 𝓘 e) = idemTop 𝓘
@[simp] lemma idemInf_compl_eq_bot : idemInf 𝓘 e (idemCompl 𝓘 e) = idemBot 𝓘
```

#### De Morgan's Laws
```lean
@[simp] lemma idemCompl_sup : 
  idemCompl 𝓘 (idemSup 𝓘 e f) = idemInf 𝓘 (idemCompl 𝓘 e) (idemCompl 𝓘 f)
@[simp] lemma idemCompl_inf :
  idemCompl 𝓘 (idemInf 𝓘 e f) = idemSup 𝓘 (idemCompl 𝓘 e) (idemCompl 𝓘 f)
```

#### Distributivity
```lean
@[simp] lemma idemSup_inf_distrib :
  idemSup 𝓘 e (idemInf 𝓘 f g) = idemInf 𝓘 (idemSup 𝓘 e f) (idemSup 𝓘 e g)
@[simp] lemma idemInf_sup_distrib :
  idemInf 𝓘 e (idemSup 𝓘 f g) = idemSup 𝓘 (idemInf 𝓘 e f) (idemInf 𝓘 e g)
```

## The Stone Map

### Definition
```lean
def stoneMap (𝓘 : SupportIdeal) : PowQuot 𝓘 → Idem 𝓘
```

Maps equivalence classes of sets (mod 𝓘) to idempotents.

### Key Properties
```lean
theorem stone_preserves_sup : stoneMap (mk A ⊔ mk B) = idemSup (stoneMap (mk A)) (stoneMap (mk B))
theorem stone_preserves_inf : stoneMap (mk A ⊓ mk B) = idemInf (stoneMap (mk A)) (stoneMap (mk B))
theorem stone_preserves_compl : stoneMap (mk Aᶜ) = idemCompl (stoneMap (mk A))
theorem stone_injective : Function.Injective (stoneMap 𝓘)
```

## Calibration Framework

### Constructive Case
```lean
theorem finite_support_surjective :
  Function.Surjective (stoneMap FiniteSupportIdeal)
```
✅ Proven constructively

### Calibration Conjecture
```lean
-- For non-metric ideals, surjectivity requires additional axioms
axiom CalibrationConjecture (𝓘 : NonMetricIdeal) :
  Function.Surjective (stoneMap 𝓘) ↔ AxiomX
```
🔬 Precise calibration point identified

## Usage Examples

### Basic Computations
```lean
example (e f : Idem 𝓘) : idemSup 𝓘 e f = idemSup 𝓘 f e := by
  simp [idemSup_comm]

example (e : Idem 𝓘) : idemCompl 𝓘 (idemCompl 𝓘 e) = e := by
  simp [idemCompl_compl]
```

### Advanced Reasoning
```lean
example (e f g : Idem 𝓘) :
  idemInf 𝓘 e (idemSup 𝓘 f g) = idemSup 𝓘 (idemInf 𝓘 e f) (idemInf 𝓘 e g) := by
  simp  -- Distributivity handled automatically
```

## Simp Normal Forms

The simp set maintains these normal forms:
1. **Nested operations** simplify (absorption, idempotence)
2. **Complements** push inward (De Morgan)
3. **Constants** float outward (bot/top laws)
4. **Canonical ordering** for commutative operations

## Integration Points

- **Paper 2**: Bidual gap uses indicator functions as idempotents
- **Paper 3A**: Stone Window as flagship calibration example
- **Future**: Extension to more general support ideals

## Testing

Run the test suite:
```bash
lake build Papers.P3_2CatFramework.test.StoneWindow_test
```

## References

- Classical Stone representation theorem
- Bishop's constructive analysis (finite support case)
- Calibration conjectures in CRM literature