# Paper 3A Roadmap — Resuming for Publication

> **Current Phase:** Resuming Paper 3A after Paper 3B completion.  
> **Objective:** Complete final polish for Paper 3A publication as framework + two calibrated case studies.
> 
> **Paper 3B Status**: ✅ COMPLETE (September 2, 2025) - 21 axioms (honest limit of schematic encoding)
> **Axiom Discharge Progress**: 30 → 24 → 23 → 22 → **21** (PR-6/7: collision machinery discharged)
> **Paper 3A LaTeX**: Updated with new framing (framework + demos + open program + 3C roadmap)

## 📍 Current Position (September 2025 - RESUMING)

**Note on Paper 3C Location**: Paper 3C materials are located at `Papers/P3_2CatFramework/P3C_DCwAxis/` (moved from `Papers/P3C_DCwAxis/` for consolidation)

#### Infrastructure
- **Part I**: Full uniformization height theory for {0,1} levels
- **Part II Core**: Positive uniformization definitions, bridges, gap results  
- **Paper 3B ProofTheory**: COMPLETE with 0 sorries, 21 axioms (September 2, 2025)
  - Stage-based ladders solve circular dependencies
  - All collision machinery as theorems (not axioms)
  - CI guards prevent regression
- **Bicategorical framework**: Complete with coherence laws
- **Truth groupoid**: With @[simp] automation
- **CI integration**: All tests passing (1189+ build jobs), no import cycles
- **WP-D Stone Window**: COMPLETE with full Stone equivalence + Path A BooleanAlgebra transport (August 29, 2025)
  - 100+ API lemmas for Boolean algebra operations
  - 27 @[simp] lemmas for Production API with forward/inverse separation
  - Perfect symmetry in complement bridges (left/right, domain/mapped)
  - Library-style proofs with minimal complexity
  - Comprehensive cheatsheet and sanity tests

---

## 0) Executive Summary

**Paper 3A Updated Scope (as per new LaTeX):**
- **Framework**: AxCal (Axiom Calibration) with uniformizability, height calculus, orthogonal profiles
- **Two Calibrated Case Studies**: 
  - WLPO axis: ℓ∞ bidual gap at height 1
  - FT axis: UCT at height 1
- **Open Calibration Program**: Stone Window (APIs + conjectures, no new theorems claimed)
- **Future Roadmap**: DC_ω/Baire frontier explicitly deferred to Paper 3C

**Remaining Work:**  
1) Final **documentation polish** in Lean (docstrings, section headers)
2) **Lean freeze** milestone (tag repo, confirm all tests green)
3) **LaTeX finalization** with artifact index and bibliography

---

## 1) Scope & Non-Goals

### In Scope (3A Lean layer)
- ✅ **PowQuot Boolean algebra** API on support ideals with full symmetry & automation (done/near-done)
- ✅ **Mapped** variants (`mapOfLe`) incl. thresholds/non-thresholds, strict order, disjoint/order bridges, functoriality (done/near-done)
- ✅ **Left-complement** endpoints & bridges (domain & mapped) with negative forms and simp-ready orientation (done/near-done)
- ✅ **Cheatsheet** & sanity tests to make the API discoverable and robust (done/near-done)
- ◻ **Stone Window BA↔Idempotent packaging**: present clean, user-facing Lean theorems for the classical isomorphism (Workstream B)
- ◻ **UCT/FT axis minimal infrastructure** in Lean (statements, stubs or references sufficient to justify profile placement) (Workstream C)
- ◻ **Documentation pass** (docstrings, section headers, lemma groups, naming pass, `@[simp]` orientation notes) (Workstream D)
- ◻ **Lint & CI hygiene** (no sorries, green `lake build`, targeted lint warnings only) (Workstream D)

### Out of Scope (shift to 3B)
- Expanded proof-theory layers (Parts III–V)
- Additional axes beyond **WLPO** and **FT** (e.g., full DC_ω, Baire Category)
- Deeper constructive lower bounds (model-theoretic work) beyond what 3A states as a conjecture

---

### ✅ Recently Completed (January 29, 2025)

#### Stone Window Production API
- **27 @[simp] lemmas** for truly one-step automation
- **Forward/inverse separation** prevents simp loops
- **Complete Boolean preservation**: inf/sup/compl operations
- **Round-trip lemmas**: 0 sorries using Equiv machinery
- **Cheatsheet documentation** for instant discoverability

#### FT/UCT Minimal Surface
- **FT_UCT_MinimalSurface.lean**: 101 lines, 0 sorries
- **Height certificates**: UCT at height 1 on FT axis
- **Orthogonality axioms**: FT ⊬ WLPO, WLPO ⊬ FT
- **AxCalProfile structure** for two-axis profiles

#### Boolean Algebra API Enhancement  
- **100+ lemmas** for comprehensive Boolean algebra reasoning
- **Disjointness/complement characterizations**: `disjoint_mk_iff`, `isCompl_mk_iff`
- **Absorption automation**: @[simp] lemmas for automatic simplification
- **Perfect symmetry**: Left/right complement bridges for domain and mapped variants
- **Library-style proofs**: Using `compl_le_iff_compl_le` for minimal complexity
- **Complete parity**: Between domain and codomain reasoning via `mapOfLe`
- **Comprehensive testing**: Stone_BA_Sanity.lean validates all API lemmas

## 2) Deliverables & "Definition of Done"

### 2.1 Lean Deliverables (3A)
- **A1. PowQuot BA API**: Complete, symmetric, curated `@[simp]` set; helper lemmas; mapped functoriality; left-complement endpoints & bridges; **cheatsheet** section and **sanity tests**
- **A2. Stone Window (Classical)**: Packaged Lean theorems showing BA side ↔ idempotents in ℓ∞/I_𝓘; clear API surface for users (namespaces, docstrings, examples)
- **A3. FT/UCT Axis (Minimal)**: Lean statements and pointers sufficient to document the FT placement (the profile result can cite existing components; full formal proofs may be lightweight)
- **A4. Test Suite**: Green builds; sanity tests cover thresholds, non-thresholds, strict order, mapped variants, left-complement endpoints (both directions via `simp`), and functoriality round-trips
- **A5. Repo Hygiene**: No sorries; `lake build` succeeds; lints acceptable (only justified warnings); docstrings at section heads

**Lean Freeze criteria**  
- ✔ `lake build` passes for all targets  
- ✔ `Papers/P3_2CatFramework/test/Stone_BA_Sanity.lean` fully green  
- ✔ No sorries  
- ✔ Stone Window classical isomorphism exposed via a clean Lean API  
- ✔ Cheatsheet synced with actual lemma names  
- ✔ Simp/mono orientation documented to avoid loops

### 2.2 LaTeX Deliverables (start only after Lean Freeze)
- 3A paper PDF with AxCal framework + WLPO/FT profiles + Stone Window (classical + caveat + conjecture)
- Artifact index mapping paper statements to Lean files/lemmas

---

## 3) Milestones (Updated for Resumption)

**M1. Lean Scope Freeze (PowQuot + Bridges) — ✅ DONE**  
- Lock API surface & names; cheatsheet aligned; smoke tests in place  
- _DoD:_ Current PowQuot sections compile; mapped and left-complement lemmas stable; tests green

**M2. Stone Window Packaging (Classical) — ✅ DONE (January 29, 2025)**  
- Expose a **clean theorems layer**: BA quotient ↔ idempotents in ℓ∞/I_𝓘  
- One or two **primary theorems** + example snippets; docstrings explaining usage  
- _DoD:_ Users can `open` the namespace and apply the isomorphism without diving into internals

**M3. FT/UCT Axis Minimal Infra — ✅ DONE (January 29, 2025)**  
- Provide Lean entries (statements/aliases/tests) sufficient to cite the FT profile placement  
- _DoD:_ Short sanity/test scaffolding compiles; profile claims can reference Lean symbols

**M4. Lint + Docs Pass — 🟢 ACTIVE (September 2025)**  
- Complete remaining docstrings for Map variants, Left-complement bridges, Functoriality
- Verify all tests pass with current Lean/mathlib versions
- _DoD:_ Green builds; comprehensive docstrings; no critical lints

**M5. Lean Freeze & Tag — 🔵 NEXT**  
- Tag repo (e.g., `v3a-lean-freeze-sept2025`)  
- Create artifact index mapping LaTeX claims to Lean files
- _Gate to final LaTeX polish_

**M6. LaTeX 3A Finalization — 🔵 FINAL**  
- Integrate Lean artifact references into LaTeX
- Add acknowledgments and final bibliography
- Prepare submission package with reproducibility instructions

---

## 4) Detailed Work Plan (Lean)

### Workstream A — PowQuot Boolean Algebra API (polish/lock) ✅

**Files**  
- `Papers/P3_2CatFramework/P4_Meta/StoneWindow_SupportIdeals.lean`  
- `Papers/P3_2CatFramework/test/Stone_BA_Sanity.lean`

**Status highlights** *(from recent commits)*  
- Thresholds / non-thresholds / strict order ✔  
- Mapped thresholds / strict order ✔  
- Disjoint as order (domain & mapped) ✔  
- Subset→order & `mk_monotone` ✔  
- Functoriality of `mapOfLe` ✔  
- Order isomorphism when ideals coincide ✔  
- Left-complement bridges & endpoints (+ negatives, mapped) ✔  
- Cheatsheet section & sanity tests ✔

**Remaining polish**  
- [x] Final docstrings at section starts (January 29, 2025)
- [ ] Quick naming pass (aliases if aligning with mathlib conventions helps)
- [ ] Sanity: add one "both directions via `simp`" test per `_iff` lemma family

**Acceptance tests**  
- [x] `lake build Papers.P3_2CatFramework.P4_Meta.StoneWindow_SupportIdeals`  
- [x] `lake build Papers.P3_2CatFramework.test.Stone_BA_Sanity`

---

### Workstream B — Stone Window: BA ↔ Idempotents (Classical) ✅ DONE

**Objective**  
Package the classical isomorphism for support ideals into **clean Lean theorems** and small examples.

**Targets**  
- [x] Public theorems (completed January 29, 2025)
  - `stoneWindowIso : PowQuot 𝓘 ≃ LinfQuotRingIdem 𝓘 R` 
  - Clean API with `powQuotToIdem` and `idemToPowQuot` functions
  - **27 @[simp] lemmas** for truly one-step automation
- [x] Convenience lemmas:
  - Preservation of `inf/sup/complement` under the isomorphism (`powQuotToIdem_inf`, `powQuotToIdem_sup`, `powQuotToIdem_compl`)
  - Endpoint correspondences: ⊥/⊤ (`powQuotToIdem_bot`, `powQuotToIdem_top`)
  - Round-trip lemmas (`idemToPowQuot_powQuotToIdem`, `powQuotToIdem_idemToPowQuot` - 0 sorries)
  - Boolean preservation theorem (`stoneWindowIso_preserves_boolean`)
  - Forward/inverse head separation prevents simp loops

**Definition of Done**  
- [x] Users can apply the isomorphism with clean API functions
- [x] Sanity file contains comprehensive test coverage in `Stone_BA_Sanity.lean`

---

### Workstream C — FT / UCT Axis (Minimal Lean surface) ✅ DONE

**Objective**  
Provide Lean names/statements sufficient to reference the UCT placement on the FT axis in 3A.

**Tasks**  
- [x] Introduce minimal symbols/aliases or references for UCT & FT (consistent with our AxCal narrative)  
- [x] FT_UCT_MinimalSurface.lean created (101 lines, 0 sorries)
- [x] Height certificates: UCT at height 1 on FT axis (`uct_height1_cert`)
- [x] Orthogonality axioms: `FT_not_implies_WLPO`, `WLPO_not_implies_FT`
- [x] AxCalProfile structure for two-axis profiles (ftHeight, wlpoHeightIsOmega)

**DoD**  
- [x] Sanity snippet compiles and all axioms validate
- [x] UCT profile: (ftHeight := 1, wlpoHeightIsOmega := true)

---

### Workstream D — Tests, Docs, Lints, Packaging 🔵

**Tests**  
- [ ] Ensure each `_iff` lemma has a quick "both directions via `simp`" round-trip test  
- [ ] Keep `#print axioms` on theorems we highlight (advertise no extra axioms)

**Docs**  
- [x] Section docstrings: Thresholds, Non-thresholds, Strict Order (January 29, 2025)
- [ ] Complete docstrings for: Map variants, Left-complement bridges, Functoriality
- [x] Cheatsheet synced to lemma names (already present; re-verify)

**Lints**  
- [ ] Replace `simpa` → `simp` **only when** the goal is syntactically identical  
- [x] Keep `mapOfLe_compl` **without** `@[simp]` (documented to avoid loops)

**Packaging**  
- [x] Add `ARTIFACTS.md` (build instructions, commit hash, key entrypoints, test invocation)  
- [ ] Add a `paper3a-lean-freeze` tag when done

---

## 5) Commands & Paths (quick reference)

```bash
# Build core module
lake build Papers.P3_2CatFramework.P4_Meta.StoneWindow_SupportIdeals

# Run sanity tests
lake build Papers.P3_2CatFramework.test.Stone_BA_Sanity

# Grep for lingering lints (optional)
grep -n "warning:" . -R | grep -E "StoneWindow_SupportIdeals|Stone_BA_Sanity" || true
```

**Key files**
- Core: `Papers/P3_2CatFramework/P4_Meta/StoneWindow_SupportIdeals.lean`
- Tests: `Papers/P3_2CatFramework/test/Stone_BA_Sanity.lean`
- (Later) Paper: `Papers/P3_2CatFramework/paper3a/main.tex` (gated; create after Lean freeze)

---

## 6) Risks & Mitigations

- **Simp loops / orientation**  
  Mitigation: Keep `mapOfLe_compl` non-simp; document intended simp directions in docstrings

- **Name churn**  
  Mitigation: Add alias for any renames; keep cheatsheet synced

- **Scope creep into 3B**  
  Mitigation: Enforce Lean-first scope; anything beyond BA/Stone/FT minimal surfaces moves to backlog

---

## 7) Status Dashboard (Updated: September 2025 - RESUMPTION)

| Workstream | Status | Notes |
|------------|--------|-------|
| A. PowQuot BA API | ✅ DONE | 100+ lemmas, full symmetry, cheatsheet, comprehensive tests |
| B. Stone Window Packaging | ✅ DONE | Clean API with stoneWindowIso, 27 @[simp] lemmas, 0 sorries |
| C. FT/UCT Minimal Surface | ✅ DONE | FT_UCT_MinimalSurface.lean with orthogonality axioms |
| D. Lints/Docs/Packaging | 🟢 ACTIVE | Final docstring completion needed; tests verification |

---

## 8) Backlog (3B)

- Proof-theory expansions (Parts III–V)
- Additional axes (DC_ω, Baire Category) and cross-calibrations
- Stronger constructive lower bounds for Stone Window (model-theoretic)
- Metatheorems on uniformizability beyond 3A needs

---

## 9) Exit Criteria → LaTeX Phase

When M5 Lean Freeze is achieved (all DoDs above met), switch to LaTeX:
- Draft `paper3a/main.tex` with AxCal + WLPO/FT profiles + Stone Window classical theorem + caveat + conjecture
- Integrate artifact index and figure/table assets

---

## 📊 Progress Tracking

### ✅ Completed (Through September 2025)
- ✅ **100+ Boolean algebra API lemmas** for PowQuot with perfect symmetry
- ✅ **Stone Window packaging** with clean user API:
  - `stoneWindowIso` equivalence theorem (0 sorries)
  - 27 @[simp] lemmas for one-step automation
  - Boolean operation preservation (inf/sup/compl)
  - Comprehensive test coverage
- ✅ **FT/UCT minimal infrastructure**:
  - FT_UCT_MinimalSurface.lean (101 lines, 0 sorries)
  - Height certificates: UCT at height 1 on FT axis
  - Orthogonality axioms: FT ⊬ WLPO, WLPO ⊬ FT
  - AxCalProfile structure for two-axis profiles
- ✅ **Paper 3B ProofTheory**: Complete with 21 axioms
- ✅ **LaTeX paper updated** with new framing (framework + demos + program)

### 🟢 Active Work (September 2025)
- 📝 Final documentation pass (remaining docstrings)
- 🧪 Test verification with current Lean/mathlib
- 📋 Artifact index preparation

### 🔵 Next Steps
- **Lean Freeze**: Tag repo once docs/tests complete
- **LaTeX finalization**: Integrate artifact references
- **Submission preparation**: Reproducibility package