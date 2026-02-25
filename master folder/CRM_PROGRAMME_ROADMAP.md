# Constructive Reverse Mathematics Series — Programme Roadmap

**Author:** Paul Chun-Kit Lee
**Last updated:** 2026-02-24 (74 papers, programme continuing)
**For:** Writing team, Lean agents, editorial collaborators

---

## 1. What the Programme Found

**The logical cost of mathematics is the logical cost of ℝ.**

The real numbers are the sole source of logical difficulty in both mathematical physics and arithmetic geometry. Every non-constructive principle required by any physical theory or any theorem in arithmetic geometry enters through the Archimedean place — the completion of ℚ at infinity. Remove ℝ and both fields collapse to BISH.

The intuition that the continuum causes difficulty is as old as Brouwer. What is new: the uniform calibration across physics and arithmetic geometry using a single framework, the identification of u(ℝ) = ∞ as the specific mechanism forcing three fields to develop the same architecture (Hilbert space inner product, Rosati involution, Petersson inner product), the projection-vs-search distinction explaining why number theory is harder than physics, and the explanation of why multiple physical theories independently encode the Langlands correspondence.

The hierarchy of logical principles:

```
BISH  ⊂  BISH + MP  ⊂  BISH + LLPO  ⊂  BISH + WLPO  ⊂  BISH + LPO  ⊂  CLASS
```

- **BISH**: all searches bounded, all witnesses explicit.
- **MP** (Markov's Principle): unbounded search that cannot fail to terminate, terminates.
- **WLPO**: decide whether a real number equals zero.
- **LPO**: decide whether a binary sequence contains a 1.

---

## 2. Programme Architecture

### Phase 0: Physics (Papers 1–44) — COMPLETE

**Result (Paper 40):** BISH + LPO is the complete logical constitution of empirically accessible physics. LPO enters through the spectral theorem for unbounded self-adjoint operators over ℝ.

### Phase 1: Arithmetic Geometry (Papers 45–66) — COMPLETE

**DPT Framework (Papers 45–53):** Three axioms for the motive. De-omniscientising descent via geometric origin. Five conjectures exhibit LPO → BISH descent with MP residual.

**h = f Discovery (Papers 56–58, 65–66):** Self-intersection = conductor on CM abelian fourfolds. 1,220 pairs verified.

**Three-Invariant Hierarchy (Papers 59–62):** Rank r, Hodge level ℓ, Lang constant c classify the full decidability landscape.

### Phase 2: Proof Methods — FLT (Paper 68) — COMPLETE

**Result: Fermat's Last Theorem is BISH.** Wiles's 1995 proof costs BISH + WLPO (weight 1 obstruction). Kisin's p = 2 dihedral bypass is BISH throughout. 18 pages, Lean verified.

### Phase 3: Function Field Langlands (Paper 69) — COMPLETE

**Result: The function field Langlands correspondence is BISH.** Both Lafforgue proofs are BISH. Key discovery: the boundary is algebraic-vs-transcendental spectral parameters, not discrete-vs-continuous spectrum. 8 pages, Lean verified.

### Phase 4: Synthesis (Paper 70) — COMPLETE

**Result: The Archimedean Principle.** Four theorems formalising the central claim. Novel contributions: (1) physics-Langlands connections as shared logical constraint, (2) function field as lattice regularisation, (3) projection-vs-search explains physics/arithmetic gap. 8 pages, Lean verified.

### Phase 5: Reverse Characterization (Paper 72) — COMPLETE

**Result: The DPT Characterization Theorem.** Positive-definite height is NECESSARY (not just sufficient) for BISH cycle-search. Combined with Paper 70 (forward), the Archimedean Principle is a biconditional: Axiom 3 ↔ BISH cycle-search. DPT axioms are the minimal axiom set. 11 pages, ~350 lines Lean, zero sorry.

### Phase 6a: Axiom 1 Reverse (Paper 73) — COMPLETE

**Result: Standard Conjecture D is necessary for BISH morphism decidability.** Conjecture D ↔ BISH morphism decidability in a realization-compatible motivic category. Without Conjecture D, the radical of the intersection pairing is non-detachable; morphism equality requires ℚ_ℓ zero-testing → LPO. Jannsen's theorem (1992) confirms the trade-off: numerical motives are BISH but lack faithful realization. 11 pages, ~250 lines Lean, zero sorry, 4 axioms.

### Phase 6b: Axiom 2 Reverse (Paper 74) — COMPLETE

**Result: Algebraic spectrum is necessary for BISH eigenvalue decidability.** Algebraic spectrum ↔ BISH eigenvalue decidability. Without geometric origin, the full analytic Langlands spectrum (Maass forms, unramified characters) has continuous spectral parameters; eigenvalue comparison costs WLPO (equality test, not existential search). The naive "transcendental eigenvalues" framing has three fatal flaws (Weil II, linear algebra vacuum, ℓ-adic CLASS trap); the correct domain of failure is the geometric-analytic boundary. 15 pages, ~200 lines Lean, zero sorry, zero propext, 4 axioms. Peer reviewed.

### Phase 6c: Conservation Test (Paper 75) — IN PROGRESS

**Target:** CRM-calibrate the Genestier-Lafforgue semisimple local Langlands parametrization for arbitrary G. Statement costs BISH + WLPO (trace equality = eigenvalue comparison = Axiom 2). Proof costs CLASS (homological + v-topology layers).

Three-layer stratification (established via external analysis, Feb 2026):
- Algebraic layer (solidification): BISH. Mittag-Leffler holds trivially — transition maps of finite sets are split epimorphisms, lim¹ = 0 constructively. No DC needed.
- Homological layer (K-injectives): CLASS (Zorn). Čech bypass fails — v-site has infinite cohomological dimension (Scholze 2017, Prop 14.12). Animation resolves sources only, not targets (Rf! needs injective envelopes).
- Geometric layer (v-topology): CLASS (BPI). BunG is an Artin v-stack, not pro-étale. G-torsors on Fargues-Fontaine curve require v-covers to trivialize.

Conservation hypothesis: the GL parametrization is a Π²₀ arithmetic statement; the CLASS scaffolding is plausibly eliminable, with residual cost BISH + WLPO predicted by DPT (the WLPO from Axiom 2's trace-equality test, per Paper 74).

---

## 3. The Quartet (Papers 68–70, 72)

**Paper 68** says: even FLT is logically cheap. The non-constructive machinery in Wiles's proof is scaffolding, not structure.

**Paper 69** says: the Langlands correspondence itself is logically cheap. The difficulty is the base field, not the correspondence.

**Paper 70** says: the only expensive thing is ℝ. u(ℝ) = ∞ forces positive-definite descent in both physics and arithmetic. Physics projects (→ BISH). Arithmetic searches (→ BISH + MP). That's why number theory is harder than physics.

**Paper 72** says: ℝ is not just sufficient but necessary. Without positive-definite height (which requires ℝ), cycle-search costs LPO. The Archimedean Principle is a biconditional. DPT and Fargues-Scholze are a logically forced partition: discrete sector (ℝ, BISH) vs continuous sector (ℚ_p, CLASS).

**Paper 73** says: Conjecture D is not just sufficient but necessary for BISH morphism decidability. Without it, numerical and homological equivalence diverge; detecting the gap costs LPO. Jannsen's escape (numerical motives) is BISH but unfaithful — confirming the trade-off is real.

**Paper 74** says: Algebraic spectrum is not just sufficient but necessary for BISH eigenvalue decidability. Without it, eigenvalue comparison costs WLPO (not LPO) — an equality test, not an existential search. The DPT axiom system is now fully characterized: each axiom is the unique condition for its domain (canonical, not merely minimal).

---

## 4. Paper Status

| Paper | Title | Pages | Status |
|-------|-------|-------|--------|
| 1–44 | Physics phase | — | ✅ Published |
| 45–64 | Arithmetic geometry | — | ✅ Published |
| 65 | h · Nm(𝔄) = f (1,220 pairs) | — | ✅ Approved → Publish |
| 66 | Trace-zero form extension | — | 🔧 5 fixes needed |
| 67 | Synthesis monograph (45–66) | 15 | 📝 3 blanks to fill |
| 68 | **FLT is BISH** | 18 | ✅ DONE (⚠️ Lean file missing from outputs) |
| 69 | **Function field Langlands is BISH** | 8 | ✅ DONE — editorial revision needed |
| 70 | **The Archimedean Principle** | 8 | ✅ DONE — editorial revision needed |
| 71 | **Archimedean Principle in Cryptography** | — | ✅ Published |
| 72 | **DPT Characterization Theorem** | 10 | ✅ DONE — Lean verified, PDF compiled, Zenodo zip |
| 73 | **Standard Conjecture D Is Necessary** | 11 | ✅ DONE — Lean verified, PDF compiled, Zenodo zip |
| 74 | **Algebraic Spectrum Is Necessary** | 15 | ✅ DONE — Lean verified, PDF compiled, Zenodo zip, peer reviewed |
| 75 | **Conservation Test: GL LLC Calibration** | — | 🔨 IN PROGRESS |

### File Inventory (actual state of `/mnt/user-data/outputs/`)

**Active files:**
- `paper68_final.tex` / `.pdf` — Paper 68 (18pp) ✅
- `paper69_funcfield.tex` / `.pdf` — Paper 69 (8pp) ✅
- `paper70.tex` / `.pdf` — Paper 70 (8pp) ✅
- `Paper69_FuncField.lean` — Paper 69 Lean ✅
- `Paper70_Archimedean.lean` — Paper 70 Lean (328 lines) ✅

**Missing:**
- `Paper68_Final.lean` — referenced in Paper 68 but not in outputs. Regenerate from `PAPER68_LEAN_WORK_ORDER.md`.

**Retired (from earlier paper numbering):**
- `paper69.tex` / `.pdf` — was BCDT extension, now working notes
- `Paper69_BCDT.lean` — was BCDT Lean
- `Paper70_KW.lean` — was Khare-Wintenberger Lean
- `paper71.tex` / `.pdf` — was weight 1 boundary, content absorbed into Paper 68
- `Paper71_Weight1.lean` — was weight 1 Lean

### Editorial Work Remaining

**Paper 69** — 8 edit items in `paper69_edit_instructions.txt`:
1. CRITICAL: Expand Remark 3.3 into full subsection (algebraic-vs-transcendental boundary)
2. Foreground Theorem C over Theorems A/B
3. Soften "WLPO necessary" → "WLPO (no known bypass)"
4. Remove "final paper" claims (Paper 70 now exists)
5. Address derived category gap in Proposition 3.2
6. Expand §6.5 with forward reference to Paper 70
7. Fix Paper 50 reference ambiguity
8. Zenodo DOI check

**Paper 70** — remaining items:
1. Brouwer inoculation sentence
2. Trim Discussion §8 redundancy
3. Two TikZ figures (four-domain diagram + matched control experiment)
4. Minor: Paper 50 reference, Zenodo DOI

**Paper 68** — Lean file recovery from `PAPER68_LEAN_WORK_ORDER.md`

---

## 5. The Programme's Discoveries

1. **BISH + LPO = physics** (Paper 40)
2. **Three-invariant hierarchy** for motives (Papers 59–62)
3. **h · Nm(𝔄) = f** (Papers 56–58, 65–66)
4. **FLT is BISH** (Paper 68)
5. **Weight 1 obstruction: irreducible but bypassable** (Paper 68)
6. **Verification vs. certification** distinction (Paper 68 §11.6)
7. **Absolute vs. relative** constructions (Paper 68 §11.5)
8. **De-omniscientising descent** over 22 years (Paper 68 §10)
9. **Algebraic-vs-transcendental boundary** — not discrete-vs-continuous (Paper 69)
10. **Function field = lattice regularisation** (Paper 70)
11. **Physics-Langlands connections explained** via shared logical constraint (Paper 70)
12. **Projection vs. search** = why number theory harder than physics (Paper 70)
13. **The Archimedean Principle**: the logical cost of mathematics is the logical cost of ℝ (Paper 70)
14. **DPT Characterization**: Archimedean Principle is a biconditional, not just forward (Paper 72)
15. **DPT-vs-FS partition**: logically forced dichotomy — discrete/BISH vs continuous/CLASS (Paper 72)
16. **ℤ-density obstruction**: ℤ dense in ℚ_p blocks Northcott independent of algebraic considerations (Paper 72)
17. **WLPO-vs-LPO asymmetry**: Axiom 2 failure costs WLPO (equality test), Axioms 1 and 3 cost LPO (existential search) — intrinsic computational distinction (Paper 74)
18. **DPT axiom system is canonical**: each axiom is the unique condition for its domain, not merely minimal (Papers 72–74)
19. **Geometric-analytic boundary**: the correct domain of Axiom 2 failure is Langlands parameters without geometric origin, not "transcendental eigenvalues" (Paper 74)

---

## 6. Open Questions (from Papers 70–74)

1. MP gap refinement — natural domain at BISH + LLPO?
2. Langlands correspondence as CRM axiom?
3. Three spectral gaps: exactly Σ⁰₂-complete?
4. **Light condensed constructivity** — PARTIALLY RESOLVED. Gemini analysis (Feb 2026): solidification is BISH (not LPO) — Mittag-Leffler holds trivially because transition maps of finite sets are split epimorphisms, lim¹ = 0 constructively, no DC needed. Čech bypass FAILS — v-site has infinite cohomological dimension (Scholze 2017, Prop 14.12); animation resolves sources only, not targets (Rf! needs injective envelopes). Open: can bounded derived categories bypass K-injective resolutions via alternative methods?
5. ~~Axiom 1 reverse characterization~~ — **ANSWERED** by Paper 73. Yes, Conjecture D is necessary. Conjecture D ↔ BISH morphism decidability.
6. ~~Axiom 2 reverse characterization~~ — **ANSWERED** by Paper 74. Yes, algebraic spectrum is necessary. Algebraic spectrum ↔ BISH eigenvalue decidability (cost without: WLPO).
7. **Conservation conjecture** — REFINED. Three-layer stratification: algebraic layer (solidification) is BISH, homological layer (K-injectives) is CLASS (Zorn), geometric layer (v-topology) is CLASS (BPI). Paper 75 target: CRM-calibrate the Genestier-Lafforgue semisimple LLC for arbitrary G. Statement costs BISH + WLPO (trace equality = eigenvalue comparison = Axiom 2, per Paper 74). Proof costs CLASS. Conservation hypothesis: the GL parametrization is a Π²₀ arithmetic statement; the CLASS scaffolding is plausibly eliminable, with residual cost BISH + WLPO.
8. **Intermediate axiom sets** — natural axiom systems strictly between BISH and LPO for partial cycle-search decidability?
9. **Function field characterization** — does Paper 72's characterization extend to function fields with modifications to Axiom 3?

The programme continues through Paper 75, then closes with Paper 67 revision.

---

## 7. File Locations

### The Trilogy
- `paper68_final.tex` / `.pdf` — Paper 68 (18pp)
- `paper69_funcfield.tex` / `.pdf` — Paper 69 (8pp)
- `paper70.tex` / `.pdf` — Paper 70 (8pp)

### Lean (present)
- `Paper69_FuncField.lean` — zero sorry
- `Paper70_Archimedean.lean` — 328 lines, zero sorry

### Lean (missing)
- Paper68_Final.lean — regenerate from `PAPER68_LEAN_WORK_ORDER.md`

### Edit Instructions
- `paper69_edit_instructions.txt` — 8 items
- `paper70_edit_instructions.txt` — 11 items

### Programme Documents
- `CRM_PROGRAMME_ROADMAP.md` — This document
- `CRM_SESSION_HANDOFF.md` — Session handoff

### Transcripts
- `/mnt/transcripts/journal.txt` — Index

All files in `/mnt/user-data/outputs/` unless otherwise noted.
