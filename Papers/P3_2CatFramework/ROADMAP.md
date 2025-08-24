# Paper 3: Development Roadmap

## 📍 Current Position (December 2024)

### ✅ Completed
- **Part I**: Full uniformization height theory for {0,1} levels
- **Part II Core**: Positive uniformization definitions, bridges, gap results
- **Infrastructure**: Bicategorical framework, Truth groupoid, CI integration

### ⚠️ Not Yet Formalized
- Theory poset `Th`, `UL(C)`, `Frontier(C)` 
- General ladder machinery and orthogonal profiles
- Higher calibrators (UCT/FT, Baire/DC_ω axes)
- Independence assumptions and model-existence arguments

## 🎯 Roadmap

### 📅 Near-term (Low Risk, High Value)

#### 1. Truth-Family Algebra (1-2 days)
**Goal**: Prove Proposition "Products and sums" from Part II

```lean
def TruthFamily (B : Foundation → Sigma0 → Bool) : WitnessFamily :=
  { C := fun F X => Truth (B F X) }
```

**Theorems to prove**:
- `PosUL (TruthFamily (B ∧ C)) ↔ PosUL (TruthFamily B) ∧ PosUL (TruthFamily C)`
- `PosUL (TruthFamily (B ∨ C)) ↔ PosUL (TruthFamily B) ∨ PosUL (TruthFamily C)`

**Impact**: Validates algebra from Part II using existing `@[simp]` lemmas

#### 2. Monotonicity for Natural Transformations (2-3 days)
**Goal**: Functorial monotonicity of positive UL

```lean
theorem pos_monotone 
  (η : ∀ F X, C.C F X → D.C F X) :
  PosUniformizableOn W C → PosUniformizableOn W D
```

**Impact**: Key structural property, enables composition reasoning

#### 3. Simp Bridges for Axiom Tokens (1 day)
**Goal**: Smooth migration path for axiom handling

```lean
@[simp] lemma hasWLPO_iff (F : Foundation) : 
  HasWLPO F ↔ F.wlpo = true
```

**Impact**: Maintains backward compatibility during refactoring

### 📅 Medium-term (Moderate Complexity)

#### 4. UL & Frontier Layer (1 week)
**Goal**: Lightweight theory-token indexing

**Components**:
- Finite "theory token" type instead of full `Th` poset
- Compute `UL`/`Frontier` for token sets
- Ladder-independent frontiers for {0,1} story

**Impact**: Foundation for multi-axiom analysis

#### 5. HeightCertificate Structure (3-4 days)
**Goal**: Document formalized vs citation-based bounds

```lean
structure HeightCertificate (WF : WitnessFamily) where
  upper_bound : Option Nat
  upper_proof : ...  -- Formalized in Lean
  lower_citation : String  -- Reference to paper/model
```

**Impact**: Clear API for verification boundaries

#### 6. Basic Natural Transformation Infrastructure (1 week)
**Goal**: Minimal categorical machinery for witness families

**Components**:
- `WitnessNatTrans`: Component-wise natural transformations
- Composition and identity laws
- Connection to monotonicity results

**Impact**: Enables general witness family manipulation

### 📅 Long-term (After Core Stabilizes)

#### 7. Higher Axes & Calibrators (2-3 weeks)
**Goal**: Extend to UCT/FT and Baire/DC_ω axes

**Components**:
- `HasFT`, `HasDCω` as `Prop` tokens with `@[simp]` bridges
- Truth families for UCT/Baire calibrators
- Product-height results under independence assumptions

**Impact**: Full multi-dimensional height analysis

#### 8. General Ladder Machinery (Research-level)
**Goal**: Implement `h_𝓛` and orthogonal profiles

**Challenges**:
- Complex dependent type management
- Performance implications of general ladders
- Need concrete use cases to guide design

#### 9. Model-Theoretic Validation (External)
**Goal**: Connect to forcing/topos models

**Note**: Per verification policy, model existence remains citation-based

## 🔧 Implementation Guidelines

### Design Principles
1. **Incremental**: Each step builds on stable foundation
2. **Testable**: Every feature includes test coverage
3. **Compatible**: Maintain backward compatibility with `@[simp]` bridges
4. **Clean**: No import cycles, minimize dependencies

### Quality Metrics
- **Zero sorries** in production code
- **CI green** after each merge
- **Documentation** for each new API

### Dependencies
```
TruthFamily → Monotonicity → NatTrans
     ↓            ↓            ↓
UL/Frontier → HeightCert → Higher Axes
```

## 📊 Success Criteria

### Short-term (Q1 2025)
- [ ] Truth-family algebra complete
- [ ] Monotonicity theorem proven
- [ ] Basic UL/Frontier implementation

### Medium-term (Q2 2025)
- [ ] HeightCertificate API stable
- [ ] Natural transformation infrastructure
- [ ] One higher axis (e.g., HasFT) integrated

### Long-term (2025+)
- [ ] Multi-dimensional height analysis
- [ ] Complete ladder machinery (if needed)
- [ ] Paper 3 fully formalized (except model theory)

## 💡 Open Questions

1. **Ladder generality**: How general should ladder machinery be?
2. **Performance**: Will general witnesses impact compile times?
3. **API design**: Best interface for HeightCertificate users?
4. **Testing strategy**: How to test independence assumptions?

## 📚 References

- Paper 3 LaTeX: Sections on uniformization height and positive uniformization
- Existing code: `Phase2_*.lean`, `Phase3_*.lean` for patterns
- CI configs: `.github/workflows/paper3-ci.yml` for test integration