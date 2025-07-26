# Sprint 38-41 Detailed Breakdown

Foundation-Relativity implementation roadmap with day-level task breakdown for Sprints 38-41, aligned with Papers 1-3 and incorporating the established design choices.

---

## Sprint 38 — "rho4-polish" (v0.4.1 Release)

**Duration**: 7 days  
**Owner**: Claude (SWE-AI)  
**Goal**: Complete housekeeping, release v0.4.1, and prepare infrastructure for categorical development

### Day-by-Day Tasks

| Day | Task | Time/LoC | Owner | Details |
|-----|------|----------|-------|---------|
| **1** | Merge PR #36, cleanup branches | 2h | Paul | Manual merge approval, delete obsolete branches |
| **1** | Tag v0.4.1 branch feat/rho4-polish | 1h | Claude | Create release branch from main |
| **2** | Update lakefile.lean to mathlib 4.5 pin | 10 LoC | Claude | Version pin update and dependency refresh |
| **2-3** | CI cache reset, 15-minute smoke test | 4h | Claude | Reset cache, optimize CI timing to ≤70s |
| **3-5** | Artifact-evaluation zip package | 6h | Claude | `lake exe cache get`, README, submission package |
| **6** | Publish release notes, Zenodo archive | 2h | Paul | GitHub release, DOI assignment |
| **7** | Sprint retrospective | 1h | All | Review completion, plan S39 handoff |

**Exit Criteria**: 
- ✅ GitHub release v0.4.1 published
- ✅ CI green with build time ≤ 70s
- ✅ Zenodo DOI assigned
- ✅ Clean repository state for S39 development

---

## Sprint 39 — "Found.Bicategory Skeleton"

**Duration**: 7 days  
**Owner**: Math-Coder AI  
**Goal**: Implement foundational bicategory infrastructure compiling in CI

### Day-by-Day Tasks

| Day | Task | Est. LoC | Dependencies | Details |
|-----|------|----------|--------------|---------|
| **1** | CategoryTheory.Foundation enum | 40 | mathlib CategoryTheory | Hard-coded: `BISH \| ZFC \| HoTT \| DNS_TT \| RCA0` |
| **1-2** | Structure Interpretation (I1a-I3) | 70 | Foundation enum | Stub fields, I1b as `PreservesBorel : Prop` |
| **3** | Category instance on Foundation | 50 | Interpretation struct | Identity interpretation, composition |
| **4** | Bicategory Found implementation | 90 | mathlib Bicategory.Basic | Associators by `rfl`, coherence automatic |
| **5** | FoundTest.lean verification | 20 | Found bicategory | `#check associator`, hexagon identity tests |
| **6** | CI/DocGen integration | — | Claude | doc-gen.yml workflow (non-blocking) |
| **7** | PR "feat: Found bicategory skeleton" | — | Claude review | Code review, merge to main |

**Technical Notes**:
- All proofs by `simp` or `rfl` (no complex category theory yet)
- I1b field `PreservesBorel : Prop` left unproven for now
- Focus on compilation and basic structure

**Exit Criteria**:
- ✅ Module compiles without errors
- ✅ All proofs complete (no `sorry`)
- ✅ Basic bicategory laws verified
- ✅ CI integration working

---

## Sprint 40 — "Pathology 2-Functors"

**Duration**: 7 days  
**Owner**: Math-Coder AI  
**Goal**: Implement Gap, AP_Fail, RNP_Fail as contravariant 2-functors

### Day-by-Day Tasks

| Day | Task | Est. LoC | Dependencies | Details |
|-----|------|----------|--------------|---------|
| **1** | Pathology/GAP.lean groupoid | 60 | ContinuousLinearMap | Gap pathology as groupoid object |
| **2** | Pathology/APFail.lean implementation | 120 | Norm estimates, classical | AP failure groupoid + pullback lemma |
| **3** | Pathology/RNPFail.lean implementation | 120 | Banach lattice primitives | RNP failure groupoid + pullback lemma |
| **4** | GapFunctor.lean 2-functor | 80 | Pathology groupoids | Contravariant functor `Found^op → Cat` |
| **5** | GapFunctorTest.lean testing | 20 | GapFunctor | Sanity checks, `#eval` examples |
| **6** | Integration and axiom checking | — | Claude | Add to lakefile, run `check-no-axioms.sh` |
| **7** | PR "feat: pathology 2-functors" | — | Claude review | Review and merge |

**Technical Approach**:
- Each pathology as groupoid (objects = instances, morphisms = equivalences)
- Pullback preservation proven for concrete cases
- Borel-σ-algebra preservation field remains `Prop` (axiomatic)

**Exit Criteria**:
- ✅ Three pathology 2-functors implemented
- ✅ Basic functoriality proven
- ✅ Integration with Foundation bicategory
- ✅ No new axioms introduced

---

## Sprint 41 — "Gödel Boolean & Rank-One Operator"

**Duration**: 7 days  
**Owner**: Math-Coder AI  
**Goal**: Implement core Gödel-Gap construction (Paper 1 foundation)

### Day-by-Day Tasks

| Day | Task | Est. LoC | Dependencies | Details |
|-----|------|----------|--------------|---------|
| **1** | Logic/Sigma1Formula.lean | 60 | Pure Lean | Inductive type, Gödel numbering function |
| **1** | Logic/Sigma1EM.lean axiom | 20 | Sigma1Formula | `axiom sig1_em : DecidableEq Sigma1Formula` |
| **2** | logicGodelBool.lean | 30 | Sigma1EM | `def c_G : Bool` with `@[irreducible]` |
| **3** | GodelGap/Projection.lean | 40 | L2Space | Define `P_g : BoundedOp` basis projector |
| **4** | GodelGap/Operator.lean | 60 | Projection | Define `G := I - c_G • P_g` |
| **5** | Simple spectrum lemma | 40 | Operator G | Two-point spectrum `{0, 1}` (classical proof) |
| **6** | GodelGapTest.lean verification | 20 | GodelGap module | `#eval ‖G‖`, `#check isLinearIsometry` |
| **7** | PR merge and integration | — | Claude review | Code review, documentation |

**Key Design Elements**:
- **Hard-coded approach**: `Sigma1Formula` as inductive type (not computational)
- **Irreducible Boolean**: `c_G` defined via pattern matching on axiom
- **Classical proofs**: Simple spectrum analysis, no constructive constraints

**Paper 1 Alignment**:
- Implements core construction from P1 §3-4
- Sets up for Fredholm equivalence (Sprint 42)
- Establishes Gödel-operator correspondence pattern

**Exit Criteria**:
- ✅ Gödel Boolean and operator defined
- ✅ Basic spectral properties proven
- ✅ Integration with existing L2Space framework
- ✅ Foundation for Sprint 42 Fredholm work

---

## Cross-Sprint Dependencies

### Mathematical Progression
```
S38 (polish) → S39 (bicategory) → S40 (2-functors)
                                       ↓
S41 (Gödel core) ← ← ← ← ← ← ← ← ← ← ← ←
```

### Technical Dependencies
- **S39 → S40**: Foundation bicategory required for 2-functor definitions
- **S40 → S44**: Pathology 2-functors needed for obstruction theorem
- **S41 → S42**: Gödel operator core required for Fredholm equivalence

### Paper Alignment
- **Sprint 39-40**: Paper 3 (2-Categorical Framework) §2-3
- **Sprint 41**: Paper 1 (Gödel-Banach) §3-4 core construction
- **Future sprints**: Paper 1 §5-6 (Fredholm), Paper 3 §4 (obstruction)

---

## Risk Mitigation

### Technical Risks
1. **mathlib API changes**: S38 includes mathlib 4.5 pin to lock dependencies
2. **Bicategory complexity**: S39 uses simple `rfl` proofs, defers complex coherence
3. **Axiom creep**: Regular `check-no-axioms.sh` runs to monitor axiom usage

### Schedule Risks
1. **S39 delay**: S40-41 can proceed in parallel if bicategory basics work
2. **Integration issues**: Daily CI checks prevent accumulation of build breaks
3. **Review bottlenecks**: Claude provides infrastructure support throughout

### Quality Assurance
- **Zero-sorry policy**: Maintained across all sprints
- **Daily builds**: CI integration prevents regression
- **Paper alignment**: Regular cross-reference with P1/P3 source material

---

## Success Metrics

### Sprint 38 Completion
- [x] v0.4.1 release published
- [x] CI optimized to ≤70s
- [x] Clean repository for S39

### Sprint 39 Completion
- [ ] Foundation bicategory compiling
- [ ] Basic category laws verified
- [ ] DocGen integration working

### Sprint 40 Completion
- [ ] Three pathology 2-functors implemented
- [ ] Functoriality proven
- [ ] Integration complete

### Sprint 41 Completion
- [ ] Gödel Boolean and operator defined
- [ ] Spectrum analysis complete
- [ ] Foundation for Paper 1 established

---

*Sprint breakdown: Foundation-Relativity S38-S41*  
*Mathematical focus: Papers 1&3 infrastructure*  
*Timeline: 4 weeks, parallel development ready*