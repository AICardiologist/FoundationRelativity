# Constructive Reverse Mathematics Series — Programme Roadmap

**Author:** Paul Chun-Kit Lee
**Last updated:** 2026-02-25 (75 papers, editorial complete)
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

### Phase 6c: Conservation Test (Paper 75) — COMPLETE

**Result: DPT passes its first external validation test.** The Genestier-Lafforgue semisimple LLC for arbitrary G decomposes into three independently calibrated layers. Statement costs BISH + WLPO; proof costs CLASS; conservation gap of two levels (WLPO < CLASS). DPT Axiom 2 correctly predicts the statement cost. 15 pages, ~180 lines Lean, zero sorry, zero propext, zero Classical.choice. 4 axioms. Peer reviewed (4 critical flaws corrected: solidification formula, trace trap, CLASS definition, function field qualification).

Four theorems:
- **Theorem A (Stratification):** fs_proof_cost = CLASS (join of three layers).
- **Theorem B (Statement Cost):** gl_statement_cost = WLPO (Bernstein center + Schur's lemma extract φ deterministically; residual = finite conjunction of WLPO equality tests on Bernstein block generators).
- **Theorem C (Conservation Gap):** WLPO < CLASS (two-level gap).
- **Theorem D (DPT Prediction):** Axiom 2 predicts WLPO; observed WLPO.

Three-layer stratification:
- Algebraic layer (solidification): BISH. Free generators Z[S]^■ = lim Z[S_n]; transition maps are split epimorphisms → Mittag-Leffler → lim¹ = 0 constructively. Animation for general M avoids injective envelopes. No DC needed.
- Homological layer (K-injectives): CLASS (Zorn). Čech bypass fails — v-site has infinite cohomological dimension (Scholze 2017, Prop 14.12). Animation resolves sources only, not targets (Rf! needs injective envelopes).
- Geometric layer (v-topology): CLASS (BPI). BunG is an Artin v-stack, not pro-étale. G-torsors on Fargues-Fontaine curve require v-covers to trivialize.

Conservation conjecture: whether the CLASS scaffolding is eliminable remains open.

---

## 3. The Quartet (Papers 68–70, 72)

**Paper 68** says: even FLT is logically cheap. The non-constructive machinery in Wiles's proof is scaffolding, not structure.

**Paper 69** says: the Langlands correspondence itself is logically cheap. The difficulty is the base field, not the correspondence.

**Paper 70** says: the only expensive thing is ℝ. u(ℝ) = ∞ forces positive-definite descent in both physics and arithmetic. Physics projects (→ BISH). Arithmetic searches (→ BISH + MP). That's why number theory is harder than physics.

**Paper 72** says: ℝ is not just sufficient but necessary. Without positive-definite height (which requires ℝ), cycle-search costs LPO. The Archimedean Principle is a biconditional. DPT and Fargues-Scholze are a logically forced partition: discrete sector (ℝ, BISH) vs continuous sector (ℚ_p, CLASS).

**Paper 73** says: Conjecture D is not just sufficient but necessary for BISH morphism decidability. Without it, numerical and homological equivalence diverge; detecting the gap costs LPO. Jannsen's escape (numerical motives) is BISH but unfaithful — confirming the trade-off is real.

**Paper 74** says: Algebraic spectrum is not just sufficient but necessary for BISH eigenvalue decidability. Without it, eigenvalue comparison costs WLPO (not LPO) — an equality test, not an existential search. The DPT axiom system is now fully characterized: each axiom is the unique condition for its domain (canonical, not merely minimal).

**Paper 75** says: DPT works on theorems it wasn't designed for. The GL LLC (proved by condensed/perfectoid methods that never mention DPT) has exactly the statement cost DPT predicts. The proof costs CLASS, the statement costs only WLPO, and the gap is identified precisely: homological Zorn + geometric BPI.

---

## 4. Paper Status

| Paper | Title | Pages | Status |
|-------|-------|-------|--------|
| 1–44 | Physics phase | — | ✅ Published |
| 45–64 | Arithmetic geometry | — | ✅ Published |
| 65 | h · Nm(𝔄) = f (1,220 pairs) | — | ✅ Published |
| 66 | Trace-zero form extension | 15 | ✅ DONE — Zenodo zip ready |
| 67 | Synthesis monograph (45–75) | 17 | ✅ DONE — revised to cover Papers 45–75 (biconditionals + conservation) |
| 68 | **FLT is BISH** | 18 | ✅ DONE — Lean verified (P68_WilesFLT/, 493 lines, 0 sorry), Zenodo zip |
| 69 | **Function field Langlands is BISH** | 15 | ✅ DONE — editorial complete, Zenodo zip |
| 70 | **The Archimedean Principle** | 16 | ✅ DONE — editorial complete, Zenodo zip |
| 71 | **Archimedean Principle in Cryptography** | — | ✅ Published |
| 72 | **DPT Characterization Theorem** | 10 | ✅ DONE — Lean verified, PDF compiled, Zenodo zip |
| 73 | **Standard Conjecture D Is Necessary** | 11 | ✅ DONE — Lean verified, PDF compiled, Zenodo zip |
| 74 | **Algebraic Spectrum Is Necessary** | 15 | ✅ DONE — Lean verified, PDF compiled, Zenodo zip, peer reviewed |
| 75 | **Conservation Test: GL LLC Calibration** | 15 | ✅ DONE — Lean verified, PDF compiled, Zenodo zip, peer reviewed |

### Editorial Work — COMPLETE

All editorial items for Papers 66–70 have been completed:
- **Paper 66:** Acknowledgments standardized, format-guide bibitem added.
- **Paper 67:** Major synthesis revision — now covers Papers 45–75 (was 45–66). Five new subsections: FLT (Paper 68), function field + Archimedean (Papers 69–70), DPT biconditional trilogy (Papers 72–74), conservation test (Paper 75), remaining open questions. Conclusion updated.
- **Paper 68:** Lean bundle verified complete (P68_WilesFLT/, 493 lines, 0 sorry). Acknowledgments standardized.
- **Paper 69:** All 8 edit items completed (Remark 3.3 expanded, Theorem C foregrounded, etc.). Acknowledgments standardized.
- **Paper 70:** Discussion §8.1 trimmed (redundant with rewritten intro). TikZ figures and Brouwer inoculation already present. Acknowledgments standardized.

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
20. **Three-layer stratification**: Fargues-Scholze proof decomposes into algebraic (BISH), homological (CLASS/Zorn), geometric (CLASS/BPI) — logically independent layers (Paper 75)
21. **DPT external validation**: DPT predictions match observations on a theorem proved by entirely different methods (condensed/perfectoid, not motivic) (Paper 75)
22. **Solidification is free**: algebraic layer contributes nothing to logical cost; animation avoids injective envelopes (Paper 75)
23. **Conservation gap pattern**: FLT (5 levels), GL LLC (2 levels), fun field LLC (0*) — decreasing gap correlates with increasing algebraicity of spectrum (Papers 68, 69, 75)

---

## 6. Open Questions (from Papers 70–74)

1. MP gap refinement — natural domain at BISH + LLPO?
2. Langlands correspondence as CRM axiom?
3. Three spectral gaps: exactly Σ⁰₂-complete?
4. **Light condensed constructivity** — PARTIALLY RESOLVED. Gemini analysis (Feb 2026): solidification is BISH (not LPO) — Mittag-Leffler holds trivially because transition maps of finite sets are split epimorphisms, lim¹ = 0 constructively, no DC needed. Čech bypass FAILS — v-site has infinite cohomological dimension (Scholze 2017, Prop 14.12); animation resolves sources only, not targets (Rf! needs injective envelopes). Open: can bounded derived categories bypass K-injective resolutions via alternative methods?
5. ~~Axiom 1 reverse characterization~~ — **ANSWERED** by Paper 73. Yes, Conjecture D is necessary. Conjecture D ↔ BISH morphism decidability.
6. ~~Axiom 2 reverse characterization~~ — **ANSWERED** by Paper 74. Yes, algebraic spectrum is necessary. Algebraic spectrum ↔ BISH eigenvalue decidability (cost without: WLPO).
7. **Conservation conjecture** — ESTABLISHED as open conjecture (Paper 75). Statement = WLPO, proof = CLASS, gap = 2 levels. The three-layer stratification identifies exactly where CLASS enters: homological (Zorn for K-injectives) and geometric (BPI for v-covers). The algebraic layer is free (BISH). Whether the CLASS scaffolding is eliminable via Lurie animation, prismatic cohomology, or condensed stable ∞-categories remains open. Five specific open questions posed in Paper 75 §6.5.
8. **Intermediate axiom sets** — natural axiom systems strictly between BISH and LPO for partial cycle-search decidability?
9. **Function field characterization** — does Paper 72's characterization extend to function fields with modifications to Axiom 3?

Paper 75 complete. Editorial cleanup (Papers 66–70) and Paper 67 revision complete. All Zenodo zips built. Programme closed pending Zenodo uploads.

---

## 7. Future Direction: CRMLint — Automated Logical Cost Analysis at Scale

### The Idea

The 75-paper programme audited theorems manually: decompose a proof into stages, calibrate each against BISH ⊂ MP ⊂ WLPO ⊂ LPO ⊂ CLASS, identify concentration points. This methodology can be automated and run on the entire Mathlib library (~150,000 declarations), producing a **proof technique atlas** — a systematic map of where logical difficulty lives in formalized mathematics.

### Why This Matters

CRM's deepest insight is the distinction between **logical cost** and **proof complexity**. Taylor-Wiles patching looks complex but is logically free (BISH). Weight 1 automorphic forms look routine but carry the entire logical cost of FLT (WLPO). This distinction is invisible without CRM and becomes actionable at scale: it tells you which proof techniques are scaffolding (don't try to simplify) and which are structural obstacles (focus here for breakthroughs).

### Architecture: Four Layers

**Layer 1 — Classical dependency tracer (pure metaprogramming).** Traverse Lean 4 `Environment`. For each theorem, trace transitive dependency paths to every `Classical.choice`, `Classical.em`, `propext`, `Quot.sound` callsite. Output: dependency graph showing exactly where classical content enters. No mathematical judgment required.

**Layer 2 — Pattern classifier.** Classify each Classical.choice callsite by pattern:
- `Decidable` on real equality → WLPO pattern
- `Decidable` on `∃ n, f(n) = 0` → LPO pattern
- Through `Zorn`/`zorn_preorder` → CLASS/Zorn
- Through `IsWellOrder`/well-ordering → CLASS/AC
- `Classical.em` on Σ⁰₁ predicate → MP pattern
- Through `LinearOrder` on ℝ → infrastructure (ℝ construction artifact)

**Layer 3 — Concentration analysis.** For each theorem: count distinct Classical.choice entry points, classify each (infrastructure vs essential), identify the "essential classical core" — the minimal set of steps that can't be reclassified. Output: "47 transitive Classical.choice deps; 44 infrastructure; 2 WLPO-pattern; 1 CLASS/Zorn. Essential cost: CLASS, concentrated at step X."

**Layer 4 — AI audit layer (requires LLM).** For theorems with conservation gaps (BISH-statable, CLASS-proved): predict whether the gap is eliminable. Use the 75-paper programme as training data. The DPT biconditionals (Papers 72–74) provide the theoretical framework for predictions in arithmetic geometry.

### What CRM Uniquely Contributes to AI Mathematics

Not better tactic selection (marginal value). Two deeper capabilities:

1. **Proof existence prediction.** When the conservation gap says "statement is BISH, proof is CLASS," CRM predicts a simpler proof exists. The biconditionals make this precise for DPT-classified theorems. An AI trained on CRM-annotated Mathlib learns to predict conservation gaps for unaudited theorems — generating search targets for new, simpler proofs.

2. **Discovery through a different question.** The programme found the h = f identity, the algebraic-vs-transcendental boundary, and the projection-vs-search distinction by asking "what's the logical cost?" — a question nobody else was asking. Running this question through 150,000 theorems instead of 75 may reveal patterns invisible at manual scale.

### Relationship to Condensed Mathematics / Fargues-Scholze

CRM and condensed mathematics form a logically forced partition: CRM/DPT handles the discrete sector (ℝ, BISH, cycle-search), Fargues-Scholze handles the continuous sector (ℚ_p, CLASS, categorical). They are complementary, not competing. Paper 75 showed that DPT predictions match observations on theorems proved entirely within condensed methods. The conservation conjecture (is CLASS scaffolding eliminable?) is the open interface between them.

### Concrete First Step

Build `CRMLint` — a Lean 4 library exporting `#crm_audit TheoremName`. Test against the programme's 14 existing Lean bundles (known ground truth). Run on Mathlib's `NumberTheory`, `Analysis`, and `Topology`. Publish the atlas as a standalone tool + companion paper. The 75-paper programme is the calibration dataset.

### Calibration: Known Ground Truth from the Programme

| Paper | Theorem | Predicted CRM Level | Key Concentration Point |
|-------|---------|--------------------|-----------------------|
| 68 | FLT is BISH | BISH (via Kisin bypass) | Weight 1 forms (WLPO, artefactual) |
| 69 | Fun field LLC | BISH | None (all stages BISH) |
| 70 | Archimedean Principle | LPO (with ℝ) / BISH (without) | Spectral theorem |
| 72 | DPT Characterization | Axiom 3 ↔ BISH | Positive-definite height |
| 75 | GL LLC | Statement WLPO, Proof CLASS | Zorn (homological) + BPI (geometric) |

---

## 8. File Locations

All paths relative to `~/FoundationRelativity/`.

### Active Papers
- `paper 66/paper66.tex` / `.pdf` (15pp) + `Zenodo_P66_TraceZeroForm.zip`
- `paper 67/paper67.tex` / `.pdf` (17pp) + `Zenodo_P67_MotiveDecidability.zip`
- `paper 68/paper68_final.tex` / `.pdf` (18pp) + `Zenodo_P68_WilesFLT.zip`
- `paper 69/paper69_funcfield.tex` / `.pdf` (15pp) + `Zenodo_P69_FuncField.zip`
- `paper 70/paper70.tex` / `.pdf` (16pp) + `Zenodo_P70_Archimedean.zip`
- `paper 72/paper72.tex` / `.pdf` (10pp) + `P72_DPTCharacterisation.zip`
- `paper 73/paper73.tex` / `.pdf` (11pp) + `P73_Axiom1Reverse.zip`
- `paper 74/paper74.tex` / `.pdf` (15pp) + `P74_Axiom2Reverse.zip`
- `paper 75/paper75.tex` / `.pdf` (15pp) + `P75_ConservationTest.zip`

### Programme Documents
- `master folder/master_paper_list.txt` — complete paper list with DOIs (71 active, 0 pending)
- `master folder/CRM_PROGRAMME_ROADMAP.md` — this document
- `master folder/CRM_SESSION_HANDOFF.md` — session handoff
