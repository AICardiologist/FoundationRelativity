# Paper 3: Development Roadmap

## 📍 Current Position (January 2025)

### ✅ Completed

#### Infrastructure
- **Part I**: Full uniformization height theory for {0,1} levels
- **Part II Core**: Positive uniformization definitions, bridges, gap results  
- **Bicategorical framework**: Complete with coherence laws
- **Truth groupoid**: With @[simp] automation
- **CI integration**: All tests passing, no import cycles

#### P4_Meta Framework (Parts III-VI) - COMPLETE ✅
**Build health**: All modules compile cleanly, 0 sorries, smoke tests pass

**Part III - Ladder Algebra (Core)**
- **Certificates**:
  - `ExtendIter_succ_mono`, `ExtendIter_le_mono` (stage monotonicity)
  - `ExtendIter_congr` (pointwise congruence)  
  - `HeightCertificate.lift`, `.transport` + @[simp] stage facts
- **Products/Sup**:
  - `combineCertificates` (pair) + `HeightCertificatePair.lift/.transport`
  - N-ary aggregator with max-stage summary
- **Concatenation algebra** (`concatSteps`):
  - Prefix/tail equalities: `concat_prefix_le_eq`, `concat_tail_ge_eq`
  - Boundary @[simp]: `concat_prefix_at_cut`, `concat_tail_at`
  - Identities: `concat_zero_left` (stage), `concatSteps_zero` (step-level)
  - Associativity: `concat_assoc_tail_eq`
  - Certificate movers: `prefixLiftCert`, `tailLiftCert`, `concatPairCert`
- **Normal forms**:
  - `StepNF` with `toSteps`, `takePrefix/dropPrefix`
  - **Left-nest reassociation** fully proved:
    - `concat_left_nest_eq` (j ≤ k) via `sub_tail_index` + `not_lt_sub_of_le`
    - @[simp] `ExtendIter_concat_left_nest_eq` (stage-level corollary)

**Part IV - ω-limit**
- `Extendω` + @[simp] `Extendω_Provable_iff`
- Lift helpers: `certToOmega`, `pairToOmega`, `omega_of_prefixCert`, `omega_of_tailCert`
- `Extendω_provable_congr` (global pointwise equality)

**Part V - Interfaces/Reflection**
- Imported and compiling (minor "unused variable" warnings)

**Tests**
- `Meta_Smoke_test.lean`: Comprehensive ladder/product/concat/ω tests
- `NormalForm_test.lean`: Normal form and transport coverage

### ⚠️ Not Yet Formalized
- Theory poset `Th`, `UL(C)`, `Frontier(C)` 
- General ladder machinery and orthogonal profiles
- Higher calibrators (UCT/FT, Baire/DC_ω axes)
- Independence assumptions and model-existence arguments

## 🎯 Immediate Next Steps (High-Impact)

### 1. Mirror Right-Nest Reassociation
**Goal**: Complete associativity with dual law for k ≤ j
```lean
theorem concat_right_nest_eq (k j : Nat) (hkj : k ≤ j) (A B C : Nat → Formula) :
  concatSteps j (concatSteps k A B) C = 
  concatSteps k A (concatSteps (j - k) B C)
```
- Stage corollary: @[simp] `ExtendIter_concat_right_nest_eq`
- **Impact**: Lets simp canonicalize all nestings uniformly

### 2. Bulk "Bag → ω" Helper
**Goal**: Push multiple certificates to ω in one shot
```lean
def certsToOmega
  {T : Theory} {step : Nat → Formula}
  (cs : List (Σ φ, HeightCertificate T step φ)) :
  List (Σ φ, (Extendω T step).Provable φ) :=
  cs.map (fun ⟨φ, c⟩ => ⟨φ, certToOmega c⟩)
```
**Impact**: Removes boilerplate in Part IV demos

### 3. Tighten Simp Orientation
**Goal**: Ensure deterministic normalization
- Verify all @[simp] rules orient from "compound" to "canonical"
- Check for potential loops (looks clean currently)
- **Impact**: Stable simp behavior

### 4. Clean Part V Warnings
**Goal**: Silent builds for better CI signal
- Replace unused params with `_` or add local lint exceptions
- **Impact**: Clean build output

## 📅 Near-term Roadmap (1-2 weeks)

### Normal Form Ergonomics
- Add @[simp] for `prefixLen/takePrefix/dropPrefix` (careful orientation)
- Provide simp bundle documentation

### Enhanced Bag API (Optional)
- Store `List (Σ φ, HeightCertificate T step φ)` 
- Normalize to common stage at insert time
- O(1) lookups with unified stage guarantees

## 📅 Medium-term Goals (2-4 weeks)

### Truth-Family Algebra
**Goal**: Prove "Products and sums" from Part II
```lean
def TruthFamily (B : Foundation → Sigma0 → Bool) : WitnessFamily :=
  { C := fun F X => Truth (B F X) }
```
- Prove: `PosUL (TruthFamily (B ∧ C)) ↔ PosUL (TruthFamily B) ∧ PosUL (TruthFamily C)`
- **Impact**: Validates Part II algebra

### UL & Frontier Layer
**Goal**: Lightweight theory-token indexing
- Finite "theory token" type
- Compute `UL`/`Frontier` for token sets
- **Impact**: Foundation for multi-axiom analysis

### Monotonicity Results
**Goal**: Functorial monotonicity of positive UL
```lean
theorem pos_monotone (η : ∀ F X, C.C F X → D.C F X) :
  PosUniformizableOn W C → PosUniformizableOn W D
```

## 🔭 Long-term Vision (Q2 2025+)

### Higher Axes & Calibrators
- Extend to UCT/FT and Baire/DC_ω axes
- `HasFT`, `HasDCω` as `Prop` tokens
- Product-height results under independence

### General Ladder Machinery
- Implement `h_𝓛` and orthogonal profiles
- Performance optimization for general ladders

### Model-Theoretic Validation
- Connect to forcing/topos models (citation-based per policy)

## 🏗️ Technical Debt & Polish

### Documentation
- Unify terminology (prefix/tail, cut, stage)
- Add "Using this file" headers to each module
- Create API usage examples

### Testing
- Property-based tests for concat normalization
- Regression tests for simp rules
- Performance benchmarks for large ladders

### Nice-to-Have
- **Homomorphic transport**: Generic "map" for Formula renamings
- **Library docs pass**: Consistent naming conventions
- **Quickcheck-style tests**: Randomized small index testing

## 📊 Success Metrics

### Q1 2025
- [x] P4_Meta framework complete (0 sorries)
- [x] Ladder algebra with full automation
- [x] Normal forms with reassociation
- [ ] Right-nest mirror theorem
- [ ] Bulk certificate helpers
- [ ] Clean build (no warnings)

### Q2 2025
- [ ] Truth-family algebra proven
- [ ] UL/Frontier implementation
- [ ] Monotonicity theorems
- [ ] One higher axis integrated

### 2025+
- [ ] Multi-dimensional height analysis
- [ ] Complete ladder machinery
- [ ] Paper 3 fully formalized (except model theory)

## 💡 Key Achievements

The P4_Meta framework provides a **complete, sorry-free** meta-theoretic infrastructure:
- Algebraic rewrites for ladders with @[simp] automation
- Certificate lifting/transport with provenance tracking
- ω-limit theory with instance-wise reflection
- Normalized step programs with canonical representations
- Two-phase composition with prefix/tail operations

**Current strength**: Very clean Part III + IV implementation ready for use as infrastructure in Paper 3's main arguments.

## 📚 References

- Paper 3 LaTeX: Sections on uniformization height and positive uniformization
- P4_Meta modules: `Papers/P3_2CatFramework/P4_Meta/*.lean`
- Test suite: `Meta_Smoke_test.lean`, `NormalForm_test.lean`
- CI: `.github/workflows/paper3-ci.yml`