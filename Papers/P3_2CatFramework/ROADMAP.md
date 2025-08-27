# Paper 3: Development Roadmap

## 📍 Current Position (January 27, 2025)

### ✅ Completed

#### Infrastructure
- **Part I**: Full uniformization height theory for {0,1} levels
- **Part II Core**: Positive uniformization definitions, bridges, gap results  
- **Bicategorical framework**: Complete with coherence laws
- **Truth groupoid**: With @[simp] automation
- **CI integration**: All tests passing, no import cycles

#### P4_Meta Framework Schedule Mathematics Status
**Parts 1-5**: ✅ COMPLETE - Full infrastructure with round-robin, quotas, bridges
**Part 6A**: ✅ COMPLETE - Upper bound theorems (block-closed, feasibility, packed achievability)
**Part 6B**: 🚧 IN PROGRESS - Lower bound proof needed
**Part 6C**: 🚧 TODO - Permutation lemma with Finset
**Part 6D**: 🚧 TODO - Integration with ProductHeight theorems

#### P4_Meta Framework (Other Parts) - COMPLETE ✅
**Build health**: All modules compile cleanly, 0 sorries, smoke tests pass

**Part III - Ladder Algebra (Complete)**
- **Certificates**:
  - `ExtendIter_succ_mono`, `ExtendIter_le_mono` (stage monotonicity)
  - `ExtendIter_congr` (pointwise congruence)  
  - `HeightCertificate.lift`, `.transport` + @[simp] stage facts
- **k-ary Schedules**:
  - **Parts 1-5 Infrastructure ✅ COMPLETE**:
    - `Schedule k`: Map stages to k axes with quota tracking
    - `roundRobin`: Axis i appears at stages k*n+i with `roundRobin_assign` lemma
    - Complete proof: k=2 schedule ≡ fuseSteps pattern
    - Quota invariants proven by induction
    - Block/bridge lemmas for clean testing
  - **Part 6A Mathematical Results ✅ COMPLETE**:
    - `quota_roundRobin_block_closed`: Quota at k·n+r = n + 𝟙[i<r]
    - `quotas_reach_targets_iff`: Feasibility ↔ q(i) ≤ ⌊n/k⌋ + 𝟙[i<n mod k]
    - `quotas_reach_targets_packed`: Upper bound at N* = k(H-1) + S (packed setting)
  - **Part 6B-D 🚧 IN PROGRESS**:
    - `quotas_not_reached_below_packed`: Lower bound (TODO)
    - Exact finish time N* = k(H-1) + S characterization (TODO)
    - Permutation lemma for general case (TODO with Finset)
- **Products/Sup**:
  - `combineCertificates` (pair) + `HeightCertificatePair.lift/.transport`
  - N-ary aggregator with max-stage summary
  - Batch operations: `certsToOmega`, `maxStageOfCerts`
- **Concatenation algebra** (`concatSteps`):
  - Prefix/tail equalities: `concat_prefix_le_eq`, `concat_tail_ge_eq`
  - Boundary @[simp]: `concat_prefix_at_cut`, `concat_tail_at`
  - Identities: `concat_zero_left` (stage), `concatSteps_zero` (step-level)
  - Associativity: `concat_assoc_tail_eq`
  - Certificate movers: `prefixLiftCert`, `tailLiftCert`, `concatPairCert`
- **Normal forms**:
  - `StepNF` with `toSteps`, `takePrefix/dropPrefix`
  - **Reassociation theorems** fully proved:
    - `concat_left_nest_eq` (j ≤ k) via `sub_tail_index` + `not_lt_sub_of_le`
    - `concat_right_nest_eq` (k ≤ j) dual law
    - @[simp] stage-level corollaries for both
- **Positive Families (PosFam)**:
  - Lightweight wrapper for certificate collections
  - `stage` computation via `maxStageOfCerts`
  - Union operations with stage bookkeeping
  - Batch push to ω and ω+ε: `toOmega`, `toOmegaPlus`

**Part IV - ω-limit and ω+ε (Complete)**
- **ω-limit theory**:
  - `Extendω` + @[simp] `Extendω_Provable_iff`
  - Lift helpers: `certToOmega`, `pairToOmega`, `omega_of_prefixCert`, `omega_of_tailCert`
  - `Extendω_provable_congr` (global pointwise equality)
  - Least upper bound: `Extendω_is_lub`
- **Theory order and equivalence**:
  - Preorder ≤ᵀ with reflexivity and transitivity
  - Equivalence ≃ᵀ with bidirectional inclusion
  - `theoryEqv.provable_iff` for clean rewriting
- **ω+ε theory (ExtendωPlus)**:
  - Captures provability at stages n+ε
  - Monotonicity: `ExtendωPlus_mono`, `omega_le_omegaPlus`
  - Stage inclusion: `stage_le_omegaPlus`
  - Certificate lifting: `certToOmegaPlus`, `omegaPlus_of_*`
  - Congruence: `ExtendωPlus_provable_congr`, `ExtendωPlus_equiv_of_steps_eq`
  - Re-expression: `ExtendωPlus_Provable_iff_exists_ge`

**Part V - Interfaces/Reflection**
- Collision theorems: RFN → Con → Gödel
- Complexity interfaces and strictness results

**Part VI - Stone Window**
- Boolean ring with support ideals
- Provenance discipline for classical vs Lean-proved

**Tests**
- `Meta_Smoke_test.lean`: 50+ tests covering all features
- `NormalForm_test.lean`: Normal form and transport coverage
- Full ω+ε certificate and congruence tests

### ✅ Recently Completed (January 27, 2025)

#### WP Interface Layer Hardening
- **Independent predicate**: Changed from inductive to uninterpreted axiom (prevents misuse)
- **WPA namespace isolation**: Removed re-exports for true isolation
- **Performance annotations**: Added @[inline] to key definitions
- **Axiom verification**: Minimal dependency footprint confirmed

#### Track A: DCω/Baire Frontier (COMPLETE)
- **DCw_Frontier.lean**: Core infrastructure mirroring FT pattern
- **DCwPortalWire.lean**: Axiomatizes DCω → Baire reduction
- **Height profiles**: Established (0,0,1) for Baire calibrator
- **Orthogonal products**: Gap × Baire demonstrates (1,0,1) profile
- **Independence**: DCω ⊥ WLPO ⊥ FT confirmed
- **Build status**: 0 sorries, all tests passing

### ⚠️ Not Yet Formalized
- Theory poset `Th`, `UL(C)`, `Frontier(C)` 
- General ladder machinery and orthogonal profiles
- Higher calibrators beyond DCω/Baire (e.g., WKL, Bolzano-Weierstrass)
- Independence assumptions and model-existence arguments

### Build Quality (as of 2025-01-27)
- **Mathematical Sorries**: 0 ✅ (all theorems proven)
- **Integration Sorries**: 7 ⚠️ (glue code only)
- **Build Errors**: 1 (P3_AllProofs.lean export issues)
- **Warnings**: ~15 (minor style issues)
- **Clean Architecture**: Single import surface via P4_Meta

### ⚠️ Known Issues (2025-01-27)
1. **Integration Sorries (7 total)**:
   - Paper3_Integration.lean: 3 encoding placeholders
   - Phase3_Obstruction.lean: 1 encoding placeholder
   - P3_P4_Bridge.lean: 3 bridge connections
   
2. **P3_AllProofs.lean Errors**:
   - Missing exports for: uniformization_height0, gap_has_height_one, etc.
   - Theorems exist but aren't accessible due to missing exports
   
3. **Minor Warnings**:
   - 6 unused variables in proofs
   - 7 simpa vs simp linter suggestions
   - 2 unused simp arguments

4. **Axioms (~40 intentional)**:
   - Classical mathematics interfaces
   - Paper-proven results as axioms
   - Meta-theoretic facts (collision theorems, calibrators)

## 🎯 Immediate Priorities - Completing Paper 3

### 🔶 Priority 1: WP-D Stone Window Support Ideals (Original Result)

**Goal**: Prove the algebraic isomorphism for Boolean ideals (choice-free, constructive):
```lean
Φ_𝓘 : 𝓟(ℕ)/𝓘 ≅ Idem(ℓ∞/I_𝓘)
     [A] ↦ [χ_A]
```

#### PR D1: Set Quotient & Boolean Ideal (No Rings)
- Finalize `BoolIdeal` structure with empty_mem, downward, union_mem
- Define symmetric difference `A △ B := (A \ B) ∪ (B \ A)`
- Prove equivalence relation `A ≈ B ↔ A △ B ∈ 𝓘.mem`
- Define `PowQuot 𝓘 := Quot (Setoid.mk …)`
- Sanity test: quotient rewriting works

#### PR D2: Support Ideal I_𝓘 in ℓ∞
- Define `supp x := {n | x n ≠ 0}` for `x : Linf R`
- Prove support lemmas: supp(0) = ∅, supp(x+y) ⊆ supp(x) ∪ supp(y)
- Define `I_support 𝓘 : Ideal (Linf R)` via `x ∈ I_support ↔ supp x ∈ 𝓘.mem`
- Get quotient `Linf R ⧸ I_support 𝓘`

#### PR D3: The Map Φ and Isomorphism
- Define `Idem S := {e : S | e * e = e}`
- Implement `Φ_𝓘 : PowQuot 𝓘 → Idem(Ideal.Quotient(I_support 𝓘))`
- Prove well-definedness: A ≈ B implies χ_A − χ_B ∈ I_support
- Prove bijection: injective via supp(χ_A − χ_B) = A △ B, surjective via TwoIdempotents
- Package as `stone_window_isomorphism`

### 🔶 Priority 2: WP-E Replace Axiom with Proof

**Goal**: Replace `height_product_on_fuse` axiom with proof from Part II product/sup law

#### Implementation Steps
1. Expose concrete `HeightCert` from Part II
2. Provide primitive product of certificates → `height_and` corollary
3. Define fused ladder `fuse L1 L2`
4. Prove: `HeightAt L1 a C → HeightAt L2 b D → HeightAt (fuse L1 L2) (max a b) (C ∧ D)`

#### Deliverables
- `FusedLadders.lean`: Turn axiom into lemma
- Sanity test: Replay Gap × UCT and Gap × Baire → max-height

### 🔷 Priority 3: Profile System (Optional Enhancement)

**Goal**: First-class height profile concept

```lean
structure Profile := (h_WLPO h_FT h_DCw : Nat)
```

- Auto-compute profiles from reductions to axis tokens
- Generate profile table: Gap (1,0,0), UCT (0,1,0), Baire (0,0,1)
- Products take componentwise max
- Auto-generate documentation tables

## 🚀 Execution Order (Concrete PRs)

1. **PR D1**: Set quotient & BoolIdeal (no rings)
2. **PR D2**: I_support ideal on Linf and quotient
3. **PR D3**: Define Idem, implement Φ_𝓘, prove bijection + BA hom
4. **PR E1**: Replace height_product_on_fuse axiom with proof
5. **PR Profiles**: Introduce Profile + table generator
6. **Tag release**: "P3 v1.0 — Tri-orthogonal frontiers (WLPO/FT/DCω)"

## 🎯 Part 6 Completion Roadmap (Priority - Based on Junior Professor Review)

### Immediate Next Steps (Part 6B-D)

#### 1. **Packed Lower Bound** (Finset-free, constructive)
```lean
theorem quotas_not_reached_below_packed
  (k : Nat) (hk : 0 < k) (h : Fin k → Nat)
  (H S : Nat) (hS : S ≤ k)
  (bound : ∀ i, h i ≤ H)
  (pack : ∀ i, (h i = H) ↔ i.val < S) :
  ∀ {n}, n < k*(H-1) + S → ∃ i, h i > quota (roundRobin k hk) i n
```
- Use case analysis on n = k·m + r
- If m ≤ H-2: all quotas ≤ H-1, pick any i < S
- If m = H-1 and r < S: pick i = r, its quota is H-1

#### 2. **Exact Finish Time** (Packed Case)
```lean
def Nstar (k H S : Nat) : Nat := if H = 0 then 0 else k*(H-1) + S

theorem quotas_targets_exact_packed ... :
  (∀ i, h i ≤ quota (roundRobin k hk) i n) ↔ Nstar k H S ≤ n
```
- Combine upper bound (`quotas_reach_targets_packed`) 
- With lower bound (`quotas_not_reached_below_packed`)

#### 3. **Permutation/Packing Lemma** (Small Finset module)
- Create `PartVI_Finset.lean` (10-20 lines)
- Prove existence of permutation e : Fin k ≃ Fin k
- Such that (h (e i) = H) ↔ i.val < S
- Apply packed exactness to permuted family

#### 4. **Wire into ProductHeight**
- State exact product height for k-ary products under AxisIndependent
- Add k=2 corollaries (reduce to familiar 2H-1/2H cases)

## 🔧 Issue Resolution Plan (Priority)

### Immediate (1-3 days)
1. **Fix P3_AllProofs.lean exports**:
   - Add proper exports to Phase2_UniformHeight.lean
   - Export theorem names from Phase3 modules
   - Test that P3_AllProofs.lean compiles

2. **Clean up warnings**:
   - Replace simpa with simp where suggested
   - Remove unused variables
   - Fix unused simp arguments

### Short-term (1 week)
3. **Replace integration sorries**:
   - Implement proper encoding functions in Paper3_Integration.lean
   - Complete bridge connections in P3_P4_Bridge.lean
   - Document the encoding strategy

### Medium-term (2-4 weeks)
4. **Documentation improvements**:
   - Add docstrings to all public theorems
   - Create API documentation for P4_Meta
   - Write usage examples for key features

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

## 📚 Next Papers (After P3 Completion)

### Option 1: Paper 4 - AxCal Atlas / Case Studies
**Goal**: Curated gallery of theorems with computed profiles and frontiers

- Systematic catalog of theorems on WLPO / FT / DCω axes
- Cross-axis products and tradeoffs analysis
- Lightweight "how-to port a theorem into AxCal" guide
- Profile tables for common constructive principles
- Model existence arguments for independence claims

### Option 2: Paper 2 - Height Algebra Deep-Dive
**Goal**: Self-contained exposition of uniformization/height calculus

- Clean mathematical presentation (story first, code second)
- Port key results from P3 with pedagogical focus
- Formal proofs of fused ladder properties
- Connection to reverse mathematics hierarchies
- Tutorial examples with increasing complexity

## 🔭 Long-term Vision (Q2 2025+)

### Higher Axes & Calibrators
- ✅ UCT/FT axis complete (WP-B)
- ✅ Baire/DC_ω axis complete (Track A)
- Future: WKL, Bolzano-Weierstrass calibrators
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