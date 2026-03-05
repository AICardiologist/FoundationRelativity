# Constructive Reverse Mathematics Series — Programme Roadmap

**Author:** Paul Chun-Kit Lee
**Last updated:** 2026-03-05 (103 papers; Papers 77–102 — seventeen CRMLint applications + synthesis monograph + Markman audit + structural vanishing + CY3 + BSD + motivic architecture + FLT audit + K3 Hodge capstone + Berkovich motivic audit + conservation theorems; Paper 103 — first Clinical Sub-Series paper)
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
| 76 | **CRMLint** | — | In progress (940 lines Lean, zero sorry) |
| 77 | **Explicit Hodge Decompositions for E⁴** | 21 | ✅ DONE — Lean verified (798 lines, 0 sorry), PDF compiled, Zenodo zip, peer reviewed |
| 78 | **Explicit Wild Langlands for GL₂(Q₂)** | 17 | ✅ DONE — Lean verified (354 lines, 0 sorry), PDF compiled, Zenodo zip, peer reviewed |
| 79 | **Standard Conjecture D for Abelian Fourfolds of Weil Type** | 15 | ✅ DONE — Lean verified (149 lines, 0 sorry, 0 axioms on squeeze), PDF compiled, Zenodo zip, peer reviewed |
| 80 | **Algebraic Gauss-Manin over Q(t)** | 14 | ✅ DONE — Lean verified (477 lines, 0 sorry), PDF compiled |
| 81 | **Algebraic Flat Sections / Fixed Part** | 15 | ✅ DONE — Lean verified (457 lines, 0 sorry), PDF compiled |
| 82 | **Constructive Differential Galois Theory (Kovacic)** | 15 | ✅ DONE — Lean verified (457 lines, 0 sorry) |
| 84 | **Global Flatness of Weil Classes (Exotic Trace Probe)** | 15 | ✅ DONE — v3 (positive result), Lean verified (389 lines, 0 sorry, 0 axioms) |
| 85 | **Universal Flatness of Exotic Weil Classes (Genus-4)** | 9 | ✅ DONE — Lean verified (306 lines, 0 sorry, 0 axioms on squeeze) |
| 86 | **Hodge Conjecture for Exotic Weil Classes (Kani-Rosen)** | 11 | ✅ DONE — Lean verified (0 sorry, propext+Quot.sound only) |
| 87 | **Omniscience Cost of the Hodge Condition** | — | ✅ DONE — Lean (602 lines, 1 sorry in main file) |
| 88 | **The Variational Squeeze: CM Anchors and Fermat Domination** | 12 | ✅ DONE — Lean verified (411 lines, 0 sorry) |
| 89 | **The Universal Hyperelliptic Squeeze** | 13 | ✅ DONE — Lean verified (434 lines, 0 sorry) |
| 90 | **The Squeeze Is a Microscope** (Synthesis) | 22 | ✅ DONE — no Lean (synthesis paper) |
| 91 | **Logical Cost of Unconditional Hodge** (Markman Audit) | 15 | ✅ DONE — Lean verified (668 lines, 0 sorry, 0 Classical.choice) |
| 92 | **The Computational Horizon** (Genera 5–8) | 15 | ✅ DONE — Lean verified (333 lines, 0 sorry, 0 Classical.choice) |
| 93 | **The Structural Vanishing Theorem** | 9 | ✅ DONE — Lean verified (525 lines, 0 sorry) |
| 94 | **The Normal Function Squeeze** (CY3 Griffiths Group) | 15 | ✅ DONE — Lean verified (566 lines, 0 sorry) |
| 95 | **The BSD Squeeze** (GZK Decomposition) | ~20 | ✅ DONE — Lean verified (796 lines, 58 theorems, 0 sorry) |
| 96 | **The Root Number Bifurcation** (Rank 0 BSD) | 16 | ✅ DONE — Lean verified (1033 lines, 86 theorems, 0 sorry) |
| 97 | **BSD Landscape Survey — Null Finding** (Internal Note) | ~5 | ✅ DONE — no Lean (exploratory note) |
| 98 | **The Motivic CRM Architecture** | ~25 | ✅ DONE — Lean verified (607 lines, 0 sorry, 0 Classical.choice) |
| 99 | **The Hecke Theta Series Squeeze** | 21 | ✅ DONE — Lean verified (1180 lines, 7 files, 0 sorry, 0 Classical.choice) |
| 100 | **The Kuga-Satake Bifurcation** (K3 Absolute Hodge) | 16 | ✅ DONE — Lean verified (729 lines, 0 sorry, 0 Classical.choice) |
| 101 | **CRMLint Audit of Scholze's Berkovich Motives** | 42 | ✅ DONE — no Lean bundle (CRMLint scanner application + methodology) |
| 102 | **Conservation Theorems for the CRM Programme** | — | ✅ DONE — Lean verified (6 files) |
| | | | |
| | **CLINICAL SUB-SERIES** | | |
| 103 | **The Asymptotic Penumbra: CRM of the RCT Statistical Pipeline** | 25 | ✅ DONE — Lean verified (956 lines, 10 files, 58 theorems, 4 sorry documented) |

### Paper 77 — COMPLETE

Paper 77 is a **methods paper**, not a mathematical breakthrough. The Hodge Conjecture for products of CM elliptic curves was proved by Lieberman (1968) and Deligne (1982). Paper 77 makes the existence explicit: 36 rational decompositions of Hodge (2,2) basis vectors into cup products of divisor classes, formally verified in Lean 4 by `native_decide`. The contribution is the **CRMLint Squeeze pipeline** and the **asymmetric offloading architecture** (Python CAS → Lean kernel verification), demonstrated end-to-end on a case where the answer is independently known.

Key metrics: 21 pages, 24 references, 798 lines Lean (auto-generated), 491 lines Python, ~1 hour development time (vs ~4 months for Paper 5's Schwarzschild formalization — a comparable density computation).

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
24. **Asymmetric offloading**: factoring formalization into CAS computation (Python, unlimited working memory) + kernel verification (Lean, `native_decide`) eliminates the bottleneck of making Lean compute — reducing development from months to hours for comparable-density problems (Paper 77 vs Paper 5)
25. **Function-field bridge**: `ring` replaces `native_decide`, enabling CRMLint to verify symbolic Q[x,t]-polynomial identities over moduli spaces (1-dimensional families) rather than isolated Q-points (0-dimensional). Infrastructure upgrade for all future parameterized Squeeze applications (Paper 80)
26. **Kani-Rosen algebraicity**: the hidden reciprocal involution μ(x,y)=(1/x, y/x⁵) on C_t: y²=x⁹-tx⁵+x generates D₈, splitting J(C_t) ~ A² via Kani-Rosen. Generic End(A)=ℤ → MT(A)=GSp₄ → all Hodge classes on A^n algebraic. First constructive proof of Hodge Conjecture for an exotic Weil fourfold (Paper 86)
27. **Hodge condition is WLPO**: the uniform Hodge test (is α of type (p,p)?) requires WLPO; with CM metadata it drops to BISH. First CRM analysis of a Clay Millennium Problem (Paper 87)
28. **Variational Hodge Squeeze**: for simple families where Kani-Rosen fails (no reciprocal involution), CM specialization to Fermat fiber + Shioda + VHC gives conditional algebraicity. CRMLint bifurcation: split → Kani-Rosen (unconditional); simple → CM anchor + VHC (conditional). The "reduction to surfaces" proto-pattern spans both P86 and P88 (Paper 88)
29. **Universal Hyperelliptic Squeeze**: the full 3-parameter universal family C_{a,b,c}: y²=x⁹+ax⁷+bx⁵+cx³+x has τ₊(a,b,c)=0 for all three parameter directions ∂/∂a, ∂/∂b, ∂/∂c, verified as polynomial identities in Z[a,b,c]. Palindromic locus {a=c} precisely characterized as Kani-Rosen locus. Natural endpoint of Griffiths pole reduction + Fermat domination pipeline (Paper 89)
30. **Zariski Grid Specialization**: when symbolic CAS expansion exceeds physical memory (genera 6–8), evaluate the exact rational Griffiths reduction at concrete integer fibers, verify cancellation by `norm_num`, invoke Schwartz–Zippel for generic vanishing. Discrete grid evaluation is decidable → BISH. Bypasses exponential intermediate expression swell (Paper 92)
31. **Structural Vanishing Theorem**: τ₊ = 0 is not a computational accident but a structural necessity forced by two algebraic properties: oddness f(−x) = −f(x) and unit leading/trailing coefficients. Two independent proofs (hypergeometric via Varchenko exponents, topological via Deligne regularity). Explanation has same logical profile as computation: BISH backbone, CLASS topology (Paper 93)
32. **Normal Function Squeeze / CY3**: detection of non-trivial Griffiths group elements (Walcher source term δ(z) ≠ 0) is BISH; existence of infinitely many generators (Abel–Jacobi + Baire) is irreducibly CLASS. First CRM analysis of Calabi–Yau middle cohomology (Paper 94)
33. **Archimedean Obstruction Thesis**: CLASS content enters arithmetic geometry exclusively through the Archimedean place (Betti realization). Grothendieck's four realizations differ in CRM cost: Betti = CLASS, de Rham/étale/crystalline = BISH. The motivic framework predicts bypass strategies: reroute through non-Archimedean realizations to drop below CLASS (Paper 98)
34. **CRM(FLT) = WKL**: three CLASS→BISH excisions in the dihedral base case of modularity lifting. Poisson→Mumford (automorphic→de Rham), Deligne-Serre→forward matching (period map→étale), Chebotarev→effective bounds (analytic→arithmetic). Taylor-Wiles patching is the sole non-constructive node (WKL). Validates Paper 98 empirically (Paper 99)
35. **CRM reading of motives is predictive**: the DPT→motives→Paper 99 deductive chain generated the proof architecture, not just classified it. The v1→v2 history is evidence: the framework generated the specific repairs after referee demolition. No other motivic proposal (Voevodsky, Nori, André) can generate bypass algorithms because none distinguish realizations by logical cost (Paper 99)
36. **Archimedean dark matter**: keyword-based CRM scanners systematically miss classical content at the algebra/analysis interface. The LTE v1.0→v1.1 patch closed a 53% dark matter gap. First scan of any new domain will miss 40–60% of non-constructive content (Paper 101)
37. **Berkovich motivic signature = WKL**: Scholze's independence-of-ℓ proof via Berkovich motives has CRM signature WKL (not CLASS). The motivic 6-functor formalism provides a universal BISH skeleton; the sole structural gate is perfectoid profinite limits (WKL). 214 CRMLint alerts across two papers: 62 BISH + 65 parasitic WLPO + 26 motivational + 61 structural WKL (Paper 101)
38. **Parasitic WLPO excision**: 30.4% of alerts are parasitic WLPO from ℝ-valued norms in Huber's adic spaces. Switching to decidable ℚ-valued discrete groups eliminates them without mathematical loss — first concrete demonstration of the scan-map-classify-search-verify loop as proof engineering (Paper 101)
39. **Motivic descent as fourth mode of de-omniscientising descent**: beyond concentration (LTE), domain transfer (function field), and CM specialization (Hodge campaign), motivic descent physically excises the Archimedean obstruction by constructing a universal algebraic skeleton before any realization functor is applied (Paper 101)
40. **Asymptotic Penumbra in clinical trials**: the normal CDF Φ is the transcendental gate through which every asymptotic test passes, converting rational test statistics into irrational p-values. The band of width 2ε (Studentized Berry-Esseen) around α where significance is classically but not constructively decidable is the "Asymptotic Penumbra" — requiring BISH+MP. Clinical impact: GUSTO (z = 2.847, p ≈ 0.004) lies inside the penumbra (ε/α = 0.158); COURAGE and ISCHEMIA are BISH-decidable. Equivalence Barrier: d_min ≈ 65,127 events for penumbra < Cohen's d = 0.2. First CRM application to medicine. Same Archimedean obstruction (data → Φ) as in arithmetic geometry (étale → Betti) (Paper 103)

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

Papers 77–101 complete. The diagnostic programme (Papers 1–75) is closed. Papers 76–96 constitute the generative phase: automated logical cost analysis (Paper 76) and automated constructivisation via the CRMLint Squeeze (Papers 77–96). The function-field arc (Papers 80–83) is closed. The abelian/hyperelliptic Hodge arc (Papers 84–93) is closed. The CY3 frontier (Paper 94) and BSD arc (Papers 95–96) are closed. Paper 97 is an internal null-finding note (BSD landscape survey). Paper 98 establishes the motivic CRM architecture: Archimedean Obstruction Thesis, three calibration theorems, companion monograph. **Paper 99 closes the FLT audit:** CRM(FLT) = WKL via three CLASS→BISH excisions in the dihedral base case, validating Paper 98's predictions empirically. **Paper 100 closes the K3 Hodge campaign** with the Kuga-Satake bifurcation at ρ=20. **Paper 101 deploys CRMLint against Scholze's Berkovich motives proof of independence of ℓ**: 214 alerts, signature WKL, parasitic WLPO excision demonstrated, Archimedean dark matter discovered and patched. Methodology appendix establishes the scan-map-classify-search-verify loop with motivic descent as the paradigmatic Step 4.

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

### Concrete Next Steps (post-Paper 101)

1. **Finish Paper 76 (CRMLint Lean metaprogram).** Already 940 lines, zero sorry. Export `#crm_audit TheoremName`. Test against the programme's 14 existing Lean bundles. This is the measurement tool — everything downstream depends on it.
2. **Breen-Deligne package in Lean 4.** Paper 101 identifies this as pure BISH (integer matrices). Already in Lean 3 (LTE). Lean 4 port is lowest-risk, highest-reuse component.
3. **Geometric Satake BISH core.** Paper 101 found Satake over ℤ is BISH (algebraic MV cycles, Tannakian formalism). Formalizing for GL_n/𝔽_q tests motivic descent in code.
4. **Apply to weight-monodromy (Prediction 8.1).** Write LaTeX blueprint for motivic weight spectral sequence, scan with CRMLint, formalize BISH skeleton, axiomatize WKL gate. First predictive application.
5. Run on Mathlib's `NumberTheory`, `Analysis`, and `Topology`. Publish the atlas as a standalone tool. The 101-paper programme is the calibration dataset.

### Calibration: Known Ground Truth from the Programme

| Paper | Theorem | Predicted CRM Level | Key Concentration Point |
|-------|---------|--------------------|-----------------------|
| 68 | FLT is BISH | BISH (via Kisin bypass) | Weight 1 forms (WLPO, artefactual) |
| 69 | Fun field LLC | BISH | None (all stages BISH) |
| 70 | Archimedean Principle | LPO (with ℝ) / BISH (without) | Spectral theorem |
| 72 | DPT Characterization | Axiom 3 ↔ BISH | Positive-definite height |
| 75 | GL LLC | Statement WLPO, Proof CLASS | Zorn (homological) + BPI (geometric) |

---

## 8. Future Direction: The CRMLint Squeeze — Reverse-Engineering Classical Proofs via DAG Surgery

### Why This Works

Human mathematicians use CLASS (Zorn's Lemma, uncountable limits, topological compactness) as **compression algorithms** — they fly over the algebraic thicket and declare "a solution exists," leaving behind an ineffective result. AI models are the exact opposite: terrible at abstract, infinite-dimensional topological jumps (they hallucinate), but possess effectively infinite working memory for navigating massive, dense combinatorial thickets. If you leave `Classical.choice` enabled, the AI lazily mimics humans and uses the helicopter. If you use CRMLint to systematically ban the helicopter, you algorithmically corner the AI into playing to its inherent strength: searching the algebraic forest to find the exact matrix, cycle, or bounding polynomial that the human mathematician was too tired to compute.

### The Systematic Pipeline

To reverse-engineer a classical proof and discover new mathematics:

1. **The Scaffold.** Take a known classical theorem (or partial CLASS attempt) and write its outline in Lean 4.
2. **The X-Ray (CRMLint).** Run CRMLint. The tool maps the DAG and flags the **Classical Boundary Node** (CBN) — the exact lemma where the human invoked an infinite limit (LPO) or Excluded Middle (CLASS).
3. **The Excise.** Isolate the local Lean state at the cliff edge. Delete the CBN and apply `[-Classical]` to the environment.
4. **The Squeeze.** Hand this isolated state to an RL-trained prover (e.g., DeepSeek-Prover). Prompt: "Close this goal. You are forbidden from topological limits. Construct an explicit algebraic witness." Because the AI knows the theorem is true but is barred from the classical shortcut, its MCTS is structurally forced to invent a new algebraic bounding polynomial, finite matrix identity, or explicit invariant to bridge the gap. That invariant is novel, publishable mathematics.

### The Goldilocks Zone

This pipeline works only for conjectures where the classical helicopter has already landed (an ineffective CLASS proof exists) or where the cliff boundary is strictly narrowed by adjacent theorems. Pointing an AI at the empty void of a totally open problem yields infinite search width and certain failure. The CRM atlas identifies the narrow-cliff targets.

### Original Targets (from planning phase)

**Target 1: CM Fourfold Cycles — COMPLETED (Paper 77).** Result: E⁴ has no exotic Weil classes. The Anderson obstruction does not apply to non-simple products. Deterministic collapse — no search needed. The initial target (finding exotic cycle classes) was refuted by the computation itself. Pivoted to the Complete Constructive Hodge Theorem: 36 explicit decompositions, all verified.

**Target 2: The Local Langlands Correspondence for GL₂(ℚ₂) Is Constructively Decidable → Paper 78.** Harris–Taylor proved the LLC for GL_n using global Shimura varieties (CLASS, ineffective). Bushnell–Kutzko proved local representations are induced from finite "types" (BISH). An algebraic formula mapping the type directly to the Galois parameter must exist. The CRMLint Squeeze bans the global trace formula and forces explicit matching of character polynomials to Galois traces. First test case: GL₂(ℚ₂) at minimal conductor.

**Target 3: Standard Conjecture D for Abelian Fourfolds of Weil Type Is Constructively Decidable → Paper 79.** Homological = numerical equivalence is known for dim ≤ 3 (Lieberman). Open for dim 4. For generic abelian fourfolds of Weil type (where E⁴'s approach fails because exotic classes genuinely exist), the Squeeze verifies positive-definiteness of the cup-product Gram matrix on the exotic subspace. Deterministic collapse to ℚ-linear algebra.

### Paper 77: Explicit Hodge Decompositions for E⁴ — COMPLETE

Title: *Explicit Hodge Decompositions for E⁴ via Automated De-Omniscientisation*.
DOI: 10.5281/zenodo.18777596

Executed Target 1 (CM fourfold). The mathematical result is a known consequence of Lieberman/Deligne — the paper is transparent about this. The contribution is the pipeline:
1. CRMLint Squeeze protocol formalized (Scaffold → X-Ray → Excise → Squeeze).
2. Asymmetric offloading: Python CAS (exact ℚ-algebra) → Lean 4 (`native_decide` verification).
3. Deterministic collapse: the problem reduced from CLASS existence to a 36×36 linear system over ℚ.
4. Engineering documented: `noncomputable` trap, token overflow, sparse match encoding (6020→798 lines).
5. Self-correction: methodology caught hallucinated target (exotic classes on non-simple variety).

Key finding: E⁴ has no exotic Weil classes (dim Hodge = dim div. products = 36). All 36 decompositions verified. MCTS mode untested — deterministic collapse made it unnecessary.

### Paper 78: The Local Langlands Correspondence for GL₂(ℚ₂) Is Constructively Decidable — COMPLETE

Title: *The Local Langlands Correspondence for GL₂(ℚ₂) Is Constructively Decidable*.
DOI: 10.5281/zenodo.18789008

Test case: GL₂(ℚ₂), E = ℚ₂(i), conductor-2 character θ, 16 regular elliptic test elements. CBN: Harris–Taylor existence (CLASS). Constructive path: Bushnell–Kutzko type → character-trace matching over ℤ, verified by `decide`. Frobenius eigenvalues α₁ = 1, α₂ = -1 determined entirely by type data. Central character matching for F× elements. Descent: CLASS → BISH (maximal). 17 pages, 25 refs, 387 lines Lean (0 sorry), 623 lines Python, 2 TikZ figures. Peer reviewed (2 rounds).

### Paper 80: Algebraic Gauss-Manin via Griffiths Pole Reduction — COMPLETE

Title: *Algebraic Gauss-Manin via Griffiths Pole Reduction: A CRMLint Squeeze*.
DOI: 10.5281/zenodo.18791985

The function-field upgrade. Papers 77–78 operated on Q-arithmetic (0-dimensional points verified by `native_decide`). Paper 80 operates on Q(t)-algebra (1-dimensional moduli verified by `ring`). Test case: the Legendre family of elliptic curves y² = x(x-1)(x-t). CBN: Ehresmann fibration theorem (CLASS — continuous topology, analytic continuation, Hodge theory). Constructive path: Griffiths pole reduction in algebraic de Rham cohomology over Q[x,t], yielding the Picard-Fuchs operator L = t(1-t)D² + (1-2t)D - 1/4, the traceless Gauss-Manin connection matrix, and the hypergeometric recurrence 4(n+1)²a_{n+1} = (2n+1)²aₙ — all as polynomial identities verified by `ring`. 14 polynomial identities, 3 recurrence checks, closed form aₙ = C(2n,n)²/4^(2n). Descent: CLASS → BISH (maximal). 14 pages, 25 refs, 477 lines Lean (0 sorry), 180 lines Python, 1 TikZ figure.

Key infrastructure discovery: `ring` verifies symbolic polynomial identities over Q[x,t], enabling CRMLint to operate over families of varieties (moduli spaces) rather than isolated points. This is the critical upgrade for Papers 79+ where the parameter space is algebraic.

### Paper 81: The Fixed Part Theorem via Tensor Gauss-Manin — COMPLETE

Title: *The Fixed Part Theorem via Tensor Gauss-Manin: A CRMLint Squeeze*.

Extends Paper 80's 2×2 Gauss-Manin connection to the 4×4 tensor connection on H¹⊗H¹ via Kronecker sum M⊗I₂ + I₂⊗M. The symplectic intersection form W = (0,1,−1,0) is verified as a constant flat section by `ring`. The full kernel over Q(t) is 2-dimensional (spanned by W and K(t) = (1,t,t,t²)); restricting to constant (t-independent) vectors gives exactly span{W}, 1-dimensional — the algebraic Theorem of the Fixed Part. CBN: Deligne's Theorem of the Fixed Part (CLASS — topological monodromy representation, fundamental group, comparison theorem). Constructive path: polynomial linear algebra over Q[t], verified by `ring`. Descent: CLASS → BISH (maximal). Fourth CRMLint Squeeze application. Second function-field paper (after Paper 80).

Target: ~15 pages, ~25 refs, ~530 lines Lean (0 sorry), 1 TikZ figure.

### Paper 87: The Omniscience Cost of the Hodge Conjecture — COMPLETE

Title: *The Omniscience Cost of the Hodge Conjecture: A CRM Analysis*.

First CRM analysis of a Clay Millennium Problem. The uniform Hodge test — deciding "is α of type (p,p)?" for an arbitrary period matrix presented as Cauchy sequences — requires WLPO. When algebraic metadata is available (CM type, known Mumford-Tate group), the cost drops to BISH. Biconditional: uniform (p,p)-decidability = BISH iff algebraic metadata is available. The Shiga-Wolfart theorem provides the embedding reduction. 602 lines Lean (0 sorry). DOI: 10.5281/zenodo.18809903.

### Paper 88: Fermat Domination and the Variational Hodge Conjecture — COMPLETE

Title: *Fermat Domination and the Variational Hodge Conjecture: A CRMLint Squeeze*.

Addresses the Paper 85 family C_t: y² = x⁹ + tx⁷ + x, where the Kani-Rosen approach of Paper 86 fails (no reciprocal involution: the core g(x,t) = x⁸ + tx⁶ + 1 is NOT palindromic). Strategy: CM specialization at t = 0. At t = 0, the curve C₀: y² = x⁹ + x is dominated by the Fermat curve F₁₆ via π: x = u²/v², y = u/v⁹ (cleared-denominator identity u² = u¹⁸ + u²v¹⁶ from u¹⁶+v¹⁶=1). Pullback differentials are holomorphic (a+b=8≤15). Paper 85 trace vanishing (τ₊ = 0) gives the exotic class as a global flat section. Two CLASS axioms complete the chain: (1) Shioda's Fermat Hodge Conjecture (algebraicity at t=0), (2) the Variational Hodge Conjecture (spreading to generic t). Result is CONDITIONAL on VHC. CRMLint bifurcation: split families (P86) → Kani-Rosen → unconditional; simple families (P88) → CM anchor + VHC → conditional. Tenth CRMLint Squeeze. 15 pages, 26 refs, 411 lines Lean (0 sorry). DOI: 10.5281/zenodo.18809905.

### Paper 89: Absolute Hodge Classes for the Universal Hyperelliptic Weil Locus — COMPLETE

Title: *Absolute Hodge Classes for the Universal Hyperelliptic Weil Locus: A CRMLint Squeeze*.

Upgrade from P88's 1-parameter family to the universal 3-parameter hyperelliptic Weil family C_{a,b,c}: y² = x⁹ + ax⁷ + bx⁵ + cx³ + x. Strategy:

1. **Q(a,b,c) CAS upgrade.** Compute the full 4×4 Gauss-Manin connection matrix M₊(a,b,c) for V₊ over the 3-parameter function field Q(a,b,c). The connection coefficients are rational functions in a,b,c.
2. **Universal trace vanishing.** Verify τ₊(a,b,c) = tr(M₊(a,b,c)) = 0 as a multivariate polynomial identity, confirmed by Lean's `ring` tactic.
3. **Fermat anchor.** At (a,b,c) = (0,0,0), the family specializes to C₀: y² = x⁹ + x, which is dominated by F₁₆ (Paper 88's Fermat covering).
4. **Universal Absolute Hodge (conditional on VHC).** The flat section is algebraic at the Fermat fiber (Shioda) and extends to the entire 3D hyperelliptic Weil locus by the Variational Hodge Conjecture.

Why piecemeal fails: the set of families with algebraic structure (palindromic core, CM specializations, etc.) is a countable union of algebraic subvarieties of the 3D parameter space — measure zero by Baire Category. The universal family is the only honest target.

Key technical challenges:
- The 4×4 connection matrix has rational function entries in three variables; Griffiths pole reduction produces large intermediate expressions.
- Lean's `ring` must verify multivariate identities — feasible (proven in P80–83 for single variable).
- The CAS computation may require careful polynomial GCD management to keep expression size bounded.

Dependencies: Papers 84–85 (V₊ Lagrangian structure, τ₊ = 0 for specializations), Paper 88 (Fermat anchor at origin), Paper 80 (Griffiths pole reduction pipeline).

### Paper 90: The Squeeze Is a Microscope — COMPLETE

Title: *The Squeeze Is a Microscope: Automated Constructivization from CRMLint to the Hodge Horizon*.

Synthesis monograph covering the generative phase (Papers 76-89). Documents the CRMLint Squeeze protocol and its eleven applications across Hodge theory, Langlands program, differential Galois theory, and algebraic geometry. Four main theorems: (A) Squeeze Protocol decomposes T = T_BISH ∧ T_CLASS, (B) Bifurcation of Weil locus — palindromic locus unconditional, generic complement VHC-conditional, (C) Hodge Horizon — uniform Hodge test ↔ WLPO, (D) Asymmetric Offloading — >80% BISH by line count. Reports aggregate statistics: ~5,300 lines Lean 4 across 12 papers, zero sorry. Three-part structure: Part I The Method, Part II The Campaign, Part III The Architecture. 22 pages, 35 references. No new Lean bundle (synthesis paper). DOI pending.

### Paper 91: The Logical Cost of Unconditional Hodge — COMPLETE

Title: *The Logical Cost of Unconditional Hodge: A CRM Audit of the Markman--Floccari--Fu Theorem*.

CRM audit of Markman's February 2025 unconditional proof of the Hodge Conjecture for all abelian fourfolds of Weil type (arXiv:2502.03415). Four main theorems: (A) Markman's proof decomposes into 4 BISH + 5 CLASS components (Fourier-Mukai, Orlov, Schoen, semi-regularity, secant existence); overall cost CLASS. (B) Comparison: CRMLint Squeeze achieves 90% BISH (18/20) conditional on VHC; Markman achieves 44% BISH (4/9) unconditional. Squeeze is informationally more efficient. (C) A posteriori VHC consistency — Markman's result shows VHC is not refuted for exotic Weil classes on J(C_{a,b,c}). (D) Cycle class map (de Rham-Betti comparison) is irreducibly CLASS; 20/0 ratio impossible, best achievable is 19/1. Includes explicit palindromic cycle computation on {a=c} locus via Kani-Rosen splitting (extending Paper 86). 15 pages, 25 references, 668 lines Lean (0 sorry, 0 Classical.choice in proofs). DOI: 10.5281/zenodo.18809917.

### Paper 92: Cohomological Flatness for Genera 5-8 — COMPLETE

Title: *Cohomological Flatness for Genera 5-8 via Zariski Grid Specialization: A CRMLint Squeeze*.

Extends trace vanishing from genus 4 (Papers 84–89) to genera 5–8. Genus 5: explicit polynomial identity in Z[a₁,a₂,a₃,a₄], verified by `ring`. Genera 6–8: symbolic expansion triggers exponential intermediate expression swell; bypassed via Zariski Grid Specialization — evaluate at concrete integer fibers, verify cancellation by `norm_num`, invoke Schwartz–Zippel lemma for generic vanishing. Discrete grid evaluation is a finite, terminating, decidable algorithm → BISH. Twelfth CRMLint Squeeze. 15 pages, 333 lines Lean (94 verified theorems, 0 sorry, 0 Classical.choice). DOI: 10.5281/zenodo.18816696.

### Paper 93: The Structural Vanishing Theorem — COMPLETE

Title: *The Structural Vanishing Theorem: Why Exotic Weil Classes Are Universally Flat*.

Explanatory capstone for Papers 84–92. Two independent structural proofs of τ₊ = 0:

Proof 1 (hypergeometric): substitution u = x² reduces V₊ to H¹ of a fractional local system; Aomoto–Varchenko determinant formula shows the period determinant is constant because (a) all root-root exponents cancel to zero and (b) the root-origin exponent is frozen at −1/4 by Vieta's formula (P(u) has constant term 1).

Proof 2 (topological): Deligne regularity constrains τ₊ to logarithmic poles along discriminant, {a₀=0}, {a_g=0}; σ-action forces discriminant monodromy on V₊ to be unipotent with det = 1; fixing a₀ = a_g = 1 kills boundary terms.

CRM decomposition: 13 BISH + 4 CLASS. The BISH backbone (Vieta, exponent arithmetic, intersection numbers, boundary freezing) verified in Lean 4. CLASS components (Aomoto–Varchenko, Deligne regularity, Picard–Lefschetz, Ehresmann) are documentary axiom stubs. 22 pages, 525 lines Lean (0 sorry). DOI: 10.5281/zenodo.18816989.

### Paper 94: The Griffiths Group of the Mirror Quintic — COMPLETE

Title: *The Griffiths Group of the Mirror Quintic: A CRMLint Squeeze*.

First CRM analysis of Calabi–Yau middle cohomology. Test case: mirror quintic. Walcher (2007) computed the inhomogeneous Picard–Fuchs equation for the real Lagrangian RP³ in X₅: L·T(z) = (15/8)√z. Source term is algebraic (from topology of real cycle). Expansion T = √z · Σ bₙzⁿ has b₀ = 30 (Walcher's disk count), bₙ satisfying rational recurrence.

Four theorems: (A) PF differential algebra is BISH (13 sub-results, ring/norm_num/rfl). (B) Walcher equation verified algebraically: source coefficient, b₀ = 30, recurrence at 5 indices. (C) Normal Function Squeeze: detection (δ(z) ≠ 0) is BISH; Abel–Jacobi integration and Baire category infinite generation are irreducibly CLASS. (D) Voisin decomposition: 11 BISH + 3 CLASS.

Opens new research direction: CRM audits of moduli-space geometry. Detection mechanism (algebraic source from real cycle) is BISH; existence of infinitely many generators requires CLASS (Baire). Thirteenth CRMLint Squeeze. 15 pages, 566 lines Lean (0 sorry). DOI: 10.5281/zenodo.18820969.

### Paper 95: The BSD Squeeze — COMPLETE

Title: *The BSD Squeeze: CRMLint Decomposition of the Gross-Zagier-Kolyvagin Proof*.

Fourteenth CRMLint Squeeze. First CRM audit of a Clay Millennium Problem proof. Test case: 37a1 (y²+y = x³−x, conductor 37, rank 1, w=−1). Hecke eigenvalue arithmetic (28 sub-results) verified by native_decide. Heegner point canonical height bounded by Silverman (linarith). Gross-Zagier/Kolyvagin/Rankin-Selberg axiomatized as CLASS.

Four theorems: (A) Modular Symbol Core — Hecke arithmetic strictly BISH. (B) GZK Squeeze — 15 BISH + 6 CLASS = 21 components (71% constructive). (C) Detection/Existence Bifurcation — detecting Heegner point BISH, bounding MW rank CLASS. (D) BSD Formula Audit — algebraic side BISH, analytic side CLASS.

796 lines Lean, 58 theorems, 0 sorry. DOI: 10.5281/zenodo.18821019.

### Paper 96: The Root Number Bifurcation — COMPLETE

Title: *The Root Number Bifurcation: CRM Cost of BSD Detection Controlled by the Functional Equation*.

Fifteenth CRMLint Squeeze. BSD analogue of the palindromic bifurcation (Paper 89 in Hodge campaign). For rank-0 curves (w=+1), detection of L(E,1)≠0 is purely BISH via modular symbols. For rank-1 curves (w=−1), detection requires Gross-Zagier (CLASS). The CRM cost jumps discontinuously at w=−1.

Test cases: 11a1 (rank 0, w=+1) and 37a1 (rank 1, w=−1). New content: modular symbol L(E,1)/Ω⁺ = 1/5 for 11a1 (norm_num), BSD formula verification, 2-descent excision for 37a1, universal detection/existence table across P84–96. Target ~800–1000 lines Lean, 0 sorry.

### Paper 101: CRMLint Audit of Scholze's Berkovich Motives — COMPLETE

Title: *Archimedean Dark Matter: CRMLint Audit of Scholze's Berkovich Motivic Proof of Independence of ℓ*.

First external CRMLint deployment against a major active research programme. Target: Scholze's Berkovich motivic proof of independence of ℓ for étale cohomology (two papers: motivic 6-functor formalism + motivic geometric Satake). 214 CRMLint alerts across both papers: 62 BISH (algebraic core), 65 parasitic WLPO (ℝ-valued norms in Huber's adic spaces, excisable), 26 motivational (contextual CLASS references), 61 structural WKL (profinite limits, perfectoid tilting). Overall signature: WKL.

Key findings: (1) Archimedean dark matter — v1.0 scanner missed 53% of classical content in the LTE blueprint; v1.1 patch closed the gap by adding 11 keyword + 5 anti-marker patterns for norm-filtration cutoffs, completions, and radius ordering. (2) Parasitic WLPO excision — 65 alerts (30.4%) are WLPO from Huber's use of ℝ-valued ordered groups; switching to decidable ℚ-valued groups eliminates them without mathematical loss. (3) Motivic descent validated — Scholze's bypass of the comparison isomorphism ι: Q̄_ℓ ≅ ℂ is the paradigmatic expression of Step 4 in the scan-map-classify-search-verify loop. (4) Archimedean Obstruction Thesis confirmed — CLASS enters only through Betti realization; motivic descent avoids it entirely.

Methodology appendix (Appendix C) covers: LTE calibration, Archimedean dark matter discovery, scanner patch v1.0→v1.1, concentration thesis, predictive applications (weight-monodromy, function field Langlands, Shimura positive control, BSD legacy upgrade), updated proof-engineering recipe with motivic descent. Mathematical appendix covers full LTE proof chain with CRM annotations.

42 pages, no Lean bundle (CRMLint scanner application). DOI pending.

### Paper 79: Standard Conjecture D for Abelian Fourfolds of Weil Type Is Constructively Decidable — COMPLETE

**Result:** CRMLint Squeeze bypasses Hodge-Riemann bilinear relations for the exotic Weil classes of generic abelian fourfolds of Weil type with K=Q(i). The 2-dimensional Weil subspace W_K has Gram matrix G=8I_2, verified positive definite by Sylvester's criterion via `decide` (zero axioms). Preliminary CM type sweep over Q(zeta_15) confirms Hazama-Ribet obstruction. CRM descent: CLASS → BISH. Third CRMLint application. 15 pages, 149 lines Lean (0 sorry, 0 axioms on constructive path). DOI: 10.5281/zenodo.18843129.

---

## 9. File Locations

All paths relative to `~/FoundationRelativity/`.

### Active Papers
- `paper 66/paper66.tex` / `.pdf` (15pp) + `Zenodo_P66_TraceZeroForm.zip`
- `paper 67/paper67.tex` / `.pdf` (17pp) + `Zenodo_P67_MotiveDecidability.zip`
- `paper 68/paper68.tex` / `.pdf` (18pp) + `Zenodo_P68_WilesFLT_v5.zip`
- `paper 69/paper69_funcfield.tex` / `.pdf` (15pp) + `Zenodo_P69_FuncField.zip`
- `paper 70/paper70.tex` / `.pdf` (16pp) + `Zenodo_P70_Archimedean.zip`
- `paper 72/paper72.tex` / `.pdf` (10pp) + `P72_DPTCharacterisation.zip`
- `paper 73/paper73.tex` / `.pdf` (11pp) + `P73_Axiom1Reverse.zip`
- `paper 74/paper74.tex` / `.pdf` (15pp) + `P74_Axiom2Reverse.zip`
- `paper 75/paper75.tex` / `.pdf` (15pp) + `P75_ConservationTest.zip`
- `paper 76/paper76.tex` / `.pdf` + `CRMLint.zip` (in progress)
- `paper 77/paper77.tex` / `.pdf` (21pp) + `Paper77_ExplicitHodgeE4.zip` (Zenodo ready)
- `paper 78/paper78.tex` / `.pdf` (17pp) + `Paper78_WildLanglands.zip` (Zenodo ready)
- `paper 79/paper79.tex` / `.pdf` (15pp) + `Zenodo_P79_ConjD.zip` — DOI: 10.5281/zenodo.18843129
- `paper 80/paper80.tex` / `.pdf` (15pp) — DOI: 10.5281/zenodo.18791985
- `paper 81/paper81.tex` / `.pdf` (15pp) — DOI: 10.5281/zenodo.18801814
- `paper 82/paper82.tex` / `.pdf` (15pp) — DOI: 10.5281/zenodo.18801822
- `paper 83/paper83.tex` / `.pdf` (15pp) — DOI: 10.5281/zenodo.18801826
- `paper 84/paper84.tex` / `.pdf` (15pp) — DOI: 10.5281/zenodo.18802819
- `paper 85/paper85.tex` / `.pdf` (9pp) — DOI: 10.5281/zenodo.18806608
- `paper 86/paper86.tex` / `.pdf` (11pp) — DOI: 10.5281/zenodo.18809903
- `paper 87/paper87.tex` / `.pdf` — DOI: 10.5281/zenodo.18809903
- `paper 88/paper88.tex` / `.pdf` (12pp) — DOI: 10.5281/zenodo.18809905
- `paper 89/paper89.tex` / `.pdf` (13pp) — DOI: 10.5281/zenodo.18809909
- `paper 90/paper90.tex` / `.pdf` (22pp) — DOI: 10.5281/zenodo.18809911
- `paper 91/paper91.tex` / `.pdf` (15pp) — DOI: 10.5281/zenodo.18809917
- `paper 92/paper92.tex` / `.pdf` (15pp) — DOI: 10.5281/zenodo.18816696
- `paper 93/paper93.tex` / `.pdf` (22pp) — DOI: 10.5281/zenodo.18816989
- `paper 94/paper94.tex` / `.pdf` (15pp) — DOI: 10.5281/zenodo.18820969
- `paper 95/paper95.tex` / `.pdf` (~20pp) — DOI: 10.5281/zenodo.18821019
- `paper 96/paper96.tex` / `.pdf` (16pp) — DOI: 10.5281/zenodo.18869924

### Programme Documents
- `master folder/master_paper_list.txt` — complete paper list with DOIs (93 active, 0 pending)
- `master folder/CRM_PROGRAMME_ROADMAP.md` — this document
- `master folder/CRM_SESSION_HANDOFF.md` — session handoff
