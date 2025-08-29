# Paper 3A Roadmap — Lean-First Plan

> **Prime directive:** Finish **Lean/formalization** for Paper **3A**.  
> Only after a Lean **freeze** (no sorries, green builds, tests stable) do we switch to LaTeX authoring.

---

## 0) Executive Summary

**Paper 3A scope:** A focused paper delivering:
- The **AxCal** (Axiom Calibration) framework (definitions + height calculus + orthogonal profiles)
- Two **orthogonal axes** in analysis (WLPO and FT/UCT) to demonstrate utility
- The **Stone Window** program (classical isomorphism for general support ideals, plus constructive caveat + calibration conjecture)
- A **Lean 4 artifact set** that cleanly supports the above

**Plan:**  
1) Complete & polish the **Lean layer** (PowQuot BA API, Stone Window algebra, tests, docs)  
2) When Lean is frozen, switch to **LaTeX 3A** (writing, figures, cross-refs, artifact index)

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

## 3) Milestones (Lean-first, sequential)

**M1. Lean Scope Freeze (PowQuot + Bridges) — ✅ DONE**  
- Lock API surface & names; cheatsheet aligned; smoke tests in place  
- _DoD:_ Current PowQuot sections compile; mapped and left-complement lemmas stable; tests green

**M2. Stone Window Packaging (Classical) — 🟡 ACTIVE**  
- Expose a **clean theorems layer**: BA quotient ↔ idempotents in ℓ∞/I_𝓘  
- One or two **primary theorems** + example snippets; docstrings explaining usage  
- _DoD:_ Users can `open` the namespace and apply the isomorphism without diving into internals

**M3. FT/UCT Axis Minimal Infra — 🔵 TARGETED**  
- Provide Lean entries (statements/aliases/tests) sufficient to cite the FT profile placement  
- _DoD:_ Short sanity/test scaffolding compiles; profile claims can reference Lean symbols

**M4. Lint + Docs Pass — 🔵 FINAL POLISH**  
- Resolve outstanding "try `simp`" warnings where appropriate; keep intentional `simpa` where it changes type/side  
- Section docstrings and lemma grouping; confirm `mapOfLe_compl` has **no** `@[simp]`  
- _DoD:_ Green builds; docstrings present; cheatsheet and lemma names consistent

**M5. Lean Freeze & Tag — 🔵 PENDING**  
- Tag repo (e.g., `v3a-lean-freeze`)  
- _Gate to LaTeX phase opens_

**M6. LaTeX 3A (post-freeze) — 🔵 GATED**  
- Draft + integrate Lean references; figures & tables; bibliography; submission package

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

### Workstream B — Stone Window: BA ↔ Idempotents (Classical) 🟡

**Objective**  
Package the classical isomorphism for support ideals into **clean Lean theorems** and small examples.

**Targets**  
- [ ] Public theorems (names TBD, e.g.)
  - `StoneWindow.powQuot_to_idem_iso (𝓘 : BoolIdeal) : PowQuot 𝓘 ≃o Idem (LinfQuotRing 𝓘 _)`
  - or equivalently, a Boolean algebra isomorphism packaged in an `OrderIso` with helper lemmas
- [ ] Convenience lemmas:
  - Preservation of `inf/sup/complement` under the isomorphism  
  - Endpoint correspondences: ⊥/⊤ and complement  
  - Round-trip `simp` tests and small examples

**Definition of Done**  
- [ ] Users can apply the isomorphism with `simp`/`rw` support on basic Boolean operations  
- [ ] Sanity file contains 2–3 short examples

---

### Workstream C — FT / UCT Axis (Minimal Lean surface) 🔵

**Objective**  
Provide Lean names/statements sufficient to reference the UCT placement on the FT axis in 3A.

**Tasks**  
- [ ] Introduce minimal symbols/aliases or references for UCT & FT (consistent with our AxCal narrative)  
- [ ] One small sanity lemma or example that compiles and can be cited  
- [ ] (Optional) A stubbed "profile" constant/structure if convenient for cross-referencing

**DoD**  
- [ ] Sanity snippet compiles and is linked in README/cheatsheet

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

## 7) Status Dashboard (Updated: January 29, 2025)

| Workstream | Status | Notes |
|------------|--------|-------|
| A. PowQuot BA API | 🟢 near-done | Symmetric lemmas, mapped, left-complement bridges/endpoints, cheatsheet, tests largely in place |
| B. Stone Window Packaging | 🟡 in progress | Expose clean public theorems + examples; docstrings; tests |
| C. FT/UCT Minimal Surface | 🔵 pending | Provide Lean names/statements & tiny sanity test |
| D. Lints/Docs/Packaging | 🟡 in progress | Some docstrings done (Jan 29), more needed; ARTIFACTS.md created |

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

### Completed (January 29, 2025)
- ✅ 100+ Boolean algebra API lemmas for PowQuot
- ✅ Perfect symmetry between domain and mapped operations
- ✅ Left-complement endpoints with negative forms
- ✅ Cheatsheet with comprehensive API summary
- ✅ ARTIFACTS.md with build instructions
- ✅ Initial docstrings for key sections
- ✅ LaTeX skeleton created (but gated until freeze)

### Active Work
- 🔄 Stone Window packaging for clean user API
- 🔄 Documentation completion

### Up Next
- 🔵 FT/UCT minimal infrastructure
- 🔵 Final lint and test pass
- 🔵 Lean freeze and tag