# Axiom Calibration Project Roadmap

## 📍 Current Status: WP-B FT Frontier & Part 6 Complete

### Recent Achievements (January 2025)

#### ✨ WP-B FT Frontier: Complete Analytic Calibrators
**Status**: Complete with 0 sorries  
**Key Achievement**: Fan Theorem axis orthogonal to WLPO with full calibrator suite
**Technical Details**:
- `FT_Frontier.lean`: FT → UCT (Uniform Continuity) and FT → Sperner → BFPT_n
- `FTPortalWire.lean`: Height certificate transport along implications
- Height assignments: h_{FT}(UCT) = 1, h_{WLPO}(UCT) = 0 (orthogonal axes)
- Generic `height_lift_of_imp` for certificate transport
- Full test coverage in `FT_Frontier_Sanity.lean`
**Files**: FT_Frontier.lean, FTPortalWire.lean, Frontier_API.lean (enhanced)

#### ✅ Part 6 General Case: Complete Interface
**Status**: Complete with 0 sorries  
**Key Achievement**: Permutation bridge from packed to general case
**Technical Details**:
- `permuteSchedule`: Permute axis labels while preserving schedule structure
- `quota_perm`: Quotas invariant under permutation
- `targetsMet_permute`: Meeting targets invariant under permutation
- `IsPacking` specification for packing permutations
- `exact_finish_time_general_of_packing`: General case via permutation
**Files**: PartIII_Schedule.lean (1100+ lines, 0 sorries)

#### ✅ Frontier API & Portal Pattern (Enhanced)
**Status**: Complete with compositional surface  
**Key Achievement**: WLPO ↔ Gap portal enables automatic calibration transport
**Technical Details**:
- `ReducesTo` structure with `Trans` instance for calc chains
- Portal pattern: Any `P → WLPO` gives `P → Gap` and `HeightCert P`
- `StonePortalWire`: Wiring calibrators through the portal
- Generic `height_lift_of_imp` for transport along implications
- Complete helper lemmas for targetsMet abstraction
**Files**: Frontier_API.lean, StonePortalWire.lean, FT_Frontier.lean (new)

#### ✅ Stone Window Calibration: Elementary Implementation
**Status**: Complete with 0 sorries  
**Key Achievement**: Replaced heavy p-adic machinery with elementary modular arithmetic
**Technical Details**:
- Dyadic blocks via simple modular arithmetic: `n % 2^(k+1) = 2^k`
- Encoding infrastructure mapping bitstreams to {0,1}-valued sequences
- Full suite of calibration lemmas for WLPO-style reductions
- Monotonicity properties and clean equivalences
**Files**: StoneWindow_Calibration.lean (robust, sorry-free)

#### ✅ Part V Collision Theorems: Hybrid Implementation
**Status**: Hybrid complete (RFN→Con proven, Con→Gödel axiom)
**Key Components**:
- RFN→Con fully proven via typeclasses (`reflection_implies_consistency_proved`)
- Typeclass infrastructure: `CodesProofs`, `Sigma1Sound`, `HasReflection`
- Con→Gödel remains as explicit axiom (standard metamathematical result)
- Documentation clarified across all files to reflect hybrid status
**Files**: PartV_Collision.lean, PartV_Reflection.lean

#### ✅ Paper 3 P4_Meta: Complete Meta-theoretic Framework
**Status**: Complete with 0 sorries  
**Key Components**: Theory extension, height certificates, ladder algebra, normal forms  
**Technical Achievements**:
- ExtendIter with pointwise congruence for step function equality
- HeightCertificate with transport operations for pointwise-equal ladders
- Two-phase composition (concatSteps) with complete prefix/tail theorems
- Normal forms (StepNF) with canonical representation and @[simp] automation
- k-ary schedule abstractions with quota invariants (0 sorries!)
- Round-robin scheduling with complete bridge n ↦ (n%k, n/k)
- Part 6B exact finish time characterization N* = k(H-1) + S complete
- Part VI FT→UCT reduction with height certificate at level 1
- **NEW**: Complete FT frontier infrastructure (WP-B) with full calibrator suite
**Files**: P4_Meta/* (45+ modules including FT_Frontier), comprehensive test coverage

#### ✅ Paper 3 Phase 2: Truth-Family Algebra  
**Status**: Complete with 0 sorries  
**Key Results**: 
- Positive uniformization conjunction law using PUnit pivot
- Pins-aware uniformization refinement (reviewer feedback)
- Disjunction, monotonicity, and bridge lemmas
**Files**: Phase2_PositiveTruthAlgebra.lean, Phase2_PositivePins.lean

#### ✅ Paper 3 Phase 2: Uniformization Height Theory
**Status**: Complete with 0 sorries  
**Key Result**: Bidual gap has uniformization height = 1  
**Technical Innovation**: Robust Equiv construction avoiding dependent rewrites  
**Files**: Phase2_UniformHeight.lean, Phase2_API.lean, comprehensive tests  

#### ✅ Paper 2 Sprint E: WLPO ↔ BidualGap∃
**Status**: Complete (3 WLPO axiom sorries only)  
**Achievement**: Full equivalence theorem with c₀ witness space  

#### ✅ Paper 1: Sherman-Morrison Implementation
**Status**: Core complete with 0 sorries  
**Achievement**: Library-quality operator theory components  

---

## 🎯 Immediate Priorities - Phased Completion Plan

### Phase A — Part 6 Complete ✅
**Goal**: Complete Parts 6B–6D and integrate with product-height theorems  
**Status**: COMPLETE  
**Achievement**: Full interface with permutation bridge, only concrete construction remains

#### A1. Lock formal statements ✅
- [x] Quota formula: `quota_roundRobin_block_closed`
- [x] Feasibility criterion: `quotas_reach_targets_iff`
- [x] Packed target profile definition
- [x] Candidate exact time: N*(k, H, S)

#### A2. 6B — Lower bound for packed case ✅
- [x] Implement `quotas_not_reached_below_packed`
- [x] Prove edge cases: S = 0 ↔ H = 0, H > 0 → S > 0
- [x] Handle n < k(H-1)+S ∧ m = H-1 → r < S

#### A3. 6C — Exactness in packed case ✅
- [x] Prove `targetsMet_iff_ge_Nstar_packed`
- [x] Show targets_met_at n ↔ N*(k,H,S) ≤ n

#### A4. 6D — General case via permutation ✅ (Interface)
- [x] Define `permuteSchedule` and prove `quota_perm`
- [x] Prove `targetsMet_permute` invariance
- [x] Create `IsPacking` specification
- [x] Prove `exact_finish_time_general_of_packing`
- [ ] Construct concrete packing permutation (future work)

#### A5. Integration with portal pattern ✅
- [x] Frontier API with `⟶` notation and `Trans` instance
- [x] Portal pattern: WLPO ↔ Gap as universal adapter
- [x] StonePortalWire for automatic calibration transport

#### A6. Helper lemmas ✅
- [x] `targetsMet_antitone_targets`
- [x] `not_targetsMet_iff_exists_short`
- [x] N* bounds: lower, upper, strict monotonicity
- [x] `not_targetsMet_below_Nstar_packed_of`

#### A7. Documentation ✅
- [x] README updates for Paper 3
- [x] ROADMAP updates
- [x] Clean API with targetsMet abstraction

### Phase B — Paper hygiene and compile stability
**Goal**: Stable TeX artifact, consistent messaging  
**Status**: Not started

- [ ] Remove merge artifacts between ======= and >>>>>>> origin/main
- [ ] Fix \raef → \ref typos
- [ ] Add missing classical references (Turing 1939, Feferman 1962, Hájek–Pudlák, Beklemishev)
- [ ] Unify status messaging: framework paper with P2 WLPO↔gap, Parts III-V schematic
- [ ] Gate engineering tables with \fullversion switch

### Phase C — Stone window: constructive vs classical split
**Goal**: Turn Stone window into calibrator with new results  
**Status**: Mostly complete (robust elementary implementation, calibration lemmas added)

#### C1. Split statements
- [x] ✅ Constructive/Fin case: ℓ∞/c₀ idempotents ↔ 𝒫(ℕ)/Fin
- [ ] General support ideals (classical): arbitrary Boolean ideals isomorphism
- [ ] Add constructive caveat

#### C2. Calibration program (new results)
- [x] ✅ Elementary dyadic block implementation: `dyadicBlock k = {n | n ≠ 0 ∧ n % 2^(k+1) = 2^k}`
- [x] ✅ Encoding infrastructure: `encSet α` unions blocks, `e α n` gives {0,1}-valued sequence
- [x] ✅ Key calibration lemmas proved:
  - `e_idem`: Pointwise idempotency (e α n)² = e α n
  - `encSet_mono`, `e_mono`: Monotonicity lemmas
  - `e_zero_iff_all_false`: Encoding is 0 everywhere ↔ bitstream false
  - `e_exists_one_iff_exists_true`: Encoding has 1 ↔ bitstream has true bit
- [ ] Full WLPO reduction from surjectivity (scaffolded, needs completion)
- [ ] Prove for additional ideal families
- [ ] Record other families as conjectures

#### C3. Lean deliverable
- [x] ✅ Elementary implementation avoiding heavy p-adic machinery (0 sorries)
- [ ] Classical isomorphism for arbitrary ideals (pure algebra)

### Phase D — Meta-ladder cleanup
**Goal**: De-axiomatize RFN→Con step  
**Status**: Hybrid complete (RFN→Con proven, Con→Gödel remains axiom)

- [x] ✅ RFN→Con proven via typeclasses (`reflection_implies_consistency_proved`)
- [x] ✅ Typeclass infrastructure: `CodesProofs`, `Sigma1Sound`, `HasReflection`
- [x] ✅ Hybrid approach documented: proven parts use typeclasses, axiomatized parts clearly marked
- [ ] Full proof at abstraction level (truth in ℕ for Σ¹₀) - partially done
- [x] ✅ Con→Gödel remains as explicit axiom (`consistency_implies_godel`)
- [x] ✅ Documentation updated to clarify hybrid status in all files

### Phase E — Independence & product heights
**Goal**: Make assumptions explicit  
**Status**: Not started

- [ ] Record independence assumptions (WLPO vs FT, FT vs DC_ω)
- [ ] Cite standard models (realizability, sheaves)
- [ ] Adopt fused-ladder transfer lemma in Part VI
- [ ] Emit height certificates for composite calibrators

### Phase F — Packaging and release
**Goal**: Two clean builds + reproducible code  
**Status**: Not started

- [ ] Submission build: minimal status, no engineering tables
- [ ] Extended build: \fullversiontrue with all details
- [ ] Restructure repo layout:
  ```
  Papers/P3_Uniformization/
    Part6/FinishTime.lean
    Schedule/RoundRobin.lean
    Height/Certificates.lean
    Meta/Collision.lean
    Stone/SupportIdealIsos.lean
  ```
- [ ] Create comprehensive test suite

---

## 📊 Project Metrics

| Paper | Status | Sorries | Key Achievement |
|-------|--------|---------|-----------------|
| Paper 1 | 90% | 4 stubs | Sherman-Morrison complete |
| Paper 2 | 95% | 3 WLPO | WLPO ↔ Gap equivalence |
| Paper 3 | 95% | 0 | P4_Meta complete with general case & portal pattern |
| Paper 4 | 85% | 61 | Discrete spectral geometry |

**Total Sorry Count**: 68 (down from 200+ at project start)

### P4_Meta Framework Status
| Component | Files | Status | Key Features |
|-----------|-------|--------|--------------|
| Part III Ladders | 10 | ✅ Complete | Concat, normal forms, transport, @[simp] automation |
| Part III Schedule | 1 | ✅ Complete | General case via permutation, targetsMet abstraction |
| Part III Certificates | 3 | ✅ Complete | Height tracking, lift/transport, pointwise congruence |
| Part III ProductSup | 2 | ✅ Complete | Pair certificates, combinators, stage bookkeeping |
| Part IV ω-limit | 1 | ✅ Complete | Extendω, omega_of_prefixCert, omega_of_tailCert |
| Part V Collision | 4 | 🔄 Hybrid | RFN→Con proven, Con→Gödel axiom, collision chain |
| Part VI Calibrations | 3 | ✅ Complete | FT→UCT, Stone window, Frontier API portal pattern |
| Integration | 3 | ✅ Complete | Paper3_Integration, P3_Minimal, StonePortalWire |
| Tests | 3 | ✅ Passing | NormalForm_test, Meta_Smoke_test, Frontier_Sanity |

---

## 🚀 Long-term Vision

### Q3 2025: Mathematical Completion
- Complete all four papers with < 20 total sorries
- Achieve mathlib4 PR readiness for core components
- Publish comprehensive LaTeX documentation

### Q4 2025: Library Integration
- Submit operator theory components to mathlib4
- Create tutorial materials for axiom calibration
- Develop automated proof tactics for pathology analysis

### 2026: Extensions
- Generalize to non-separable Banach spaces
- Explore connections to descriptive set theory
- Develop computational tools for pathology detection

---

## 🔧 Technical Debt

### High Priority
- [ ] Unify notation across all papers
- [ ] Standardize sorry management strategy
- [ ] Complete regression test suite

### Medium Priority
- [ ] Performance optimization for large proofs
- [ ] Documentation generation automation
- [ ] CI/CD pipeline enhancements

### Low Priority
- [ ] Code style linting rules
- [ ] Visualization tools for 2-categories
- [ ] Interactive proof explorer

---

## 📚 Resources Needed

### Immediate
- Category theorist review for Paper 3 Phase 3
- Operator theory expert for Paper 1 Fredholm
- CI specialist for build optimization

### Future
- Descriptive set theorist for extensions
- HoTT expert for higher categorical structures
- Technical writer for documentation

---

---

## 🔬 Technical Architecture Insights

### Why P4_Meta Progress is Smoother
- **Deliberate abstraction**: Schematic language (atoms only) avoids heavy unification
- **Capabilities over commitments**: Classical dependencies isolated as axioms/typeclasses  
- **Certificates, not derivations**: HeightCertificate enables compositional reasoning
- **Local composability**: concatSteps, product/sup enable modular assembly
- **Normal forms**: StepNF provides canonical representation with automatic simplification

### Key Design Patterns
- **PUnit pivot technique**: Avoids cast issues in Equiv proofs
- **Typeclass preservation**: HBL/RE preserved through Extend automatically
- **Monotonicity infrastructure**: ExtendIter_le_mono enables systematic lifting
- **Transport operations**: Certificates move between pointwise-equal step functions
- **@[simp] automation**: Definitional equalities for frictionless stage arithmetic
- **Elementary proofs**: concat_left_nest_eq uses only core Nat lemmas (no fragile tactics)
- **Provenance discipline**: Classical vs Lean-proved results tracked

---

## ⚠️ Risk Notes & Mitigations

### Technical Risks
- **Part 6 lower bound**: Keep proofs purely arithmetic (no classical choice); rely on quota lemma; treat H=0 separately to avoid underflow
- **Permutation step**: Stick to stable partition (=H then <H); avoids sorting headaches
- **Calibration lower bounds**: Start with one concrete ideal (block ideal) for publishable result; leave broader families as conjectures
- **Status coherence**: Keep single "Scope & verification" box throughout to avoid mixed messages

---

## ✅ Quick Completion Checklist

### Phase A - Part 6
- [ ] A2: `quotas_not_reached_below_packed` proved
- [ ] A3: `exact_finish_time_packed` (iff form) proved
- [ ] A4: Permutation lemma + general exact time proved
- [ ] A5: ProductHeight uses N* engine
- [ ] A6: Property tests for small k,H,S; edge cases pass

### Phase B - Paper Hygiene
- [ ] TeX cleaned (merge markers, \ref, bib entries)
- [ ] Status messaging unified
- [ ] \fullversion switch implemented

### Phase C - Stone Window
- [x] Elementary dyadic block implementation (0 sorries)
- [x] Calibration lemmas (monotonicity, equivalences)
- [ ] Full WLPO reduction from surjectivity
- [ ] Classical support-ideal isomorphism

### Phase D - Meta-ladder
- [x] RFN_{Σ⁰₁}→Con implemented via typeclasses
- [x] Hybrid approach documented (Con→Gödel axiom)
- [ ] Complete de-axiomatization of Con→Gödel

### Phase E - Independence
- [ ] Independence hypotheses stated
- [ ] Fused-ladder transfer included

### Phase F - Packaging
- [ ] Two builds scripted
- [ ] Repo structure stable

---

**Last Updated**: January 2025  
**Next Review**: February 2025  
**Project Lead**: Axiom Calibration Team