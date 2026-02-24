# Paper 12 Edit Instructions — Consolidated
## essay_constructive_history.tex (Version 1.1, 02/09/2026)

All edits below are to be applied to the current file. Edits are grouped by type. Apply in order. Line numbers are approximate — use the **anchor string** (unique text to search for) to locate each edit point.

---

## A. LaTeX Build Fixes (apply first)

### A1. xcolor option clash (hard compile stop)

**Anchor:** `\usepackage{tikz}` (line 13)

Insert **before** `\usepackage{tikz}`:

```latex
\PassOptionsToPackage{dvipsnames}{xcolor}
```

Then change line 14 from:
```latex
\usepackage[dvipsnames]{xcolor}
```
to:
```latex
\usepackage{xcolor}
```

### A2. Hyperref duplicate destination warnings

**Anchor:** `\usepackage[hidelinks]{hyperref}` (line 10)

Change to:
```latex
\usepackage[hidelinks,hypertexnames=false]{hyperref}
```

---

## B. Terminology Consistency

### B1. Standardise "programme" throughout

Replace every instance of `program` (when referring to the research programme or any other programme) with `programme`. Exception: keep `program` only inside proper names of external software (e.g., "proof assistant" is not affected).

Specific instances to change (search for each):

- `research program` → `research programme` (appears ~10 times: lines 36, 117, 146, 301, 374, 408, 1667, 1811, and similar)
- `Our program` → `Our programme` (lines 517, 624, 1695, 1697)
- `Glimm-Jaffe constructive quantum field theory program` → `Glimm-Jaffe constructive quantum field theory programme` (line 1007)
- `Döring-Isham topos program` → `Döring-Isham topos programme` (line 1800)

Leave `programme` instances unchanged (they are already correct).

---

## C. Scope and Precision Fixes

### C1. Abstract scope sentence

**Anchor:** `This is Paper~12 in the Constructive Calibration Programme, a companion to the formal synthesis (Paper~10) \cite{Lee2026paper10}, written for a broader audience.` (line 39)

Change to:
```latex
This is Paper~12 in the Constructive Calibration Programme, a companion to the formal synthesis (Paper~10) \cite{Lee2026paper10}, written for a broader audience.
The calibration covers quantum states, static structures, and exactly solvable models; time evolution, scattering amplitudes, and real-time path integrals remain uncalibrated.
```

### C2. First use of BISH — add parenthetical gloss

**Anchor:** The first appearance of "BISH" in the body text is in the abstract (line 36). The first appearance in Section 1 is at line 59: `(Euclidean lattice path integrals---Wilson's 1974 construction \cite{Wilson1974}---are mathematically rigorous but operate on finite lattices, i.e., at BISH.)`

This is fine — the scope note at lines 136–139 defines BISH. No change needed; the GPT suggestion was already addressed by the existing scope note.

### C3. Precision fix — Paper 13 scope (line 841)

**Anchor:** `Paper~13 \cite{Lee2026paper13} formalizes this decomposition precisely.`

Change to:
```latex
Paper~13 \cite{Lee2026paper13} formalizes this decomposition for the Schwarzschild case.
```

### C4. Figure caption precision — Figure 10 (line 962)

**Anchor:** `The logical derivation chain for the Penrose singularity theorem.`

Change to:
```latex
The logical derivation chain for Schwarzschild geodesic incompleteness (exemplifying the Penrose pattern).
```

### C5. Figure caption precision — Figure 12 (lines 1619–1631)

**Anchor (inside the caption):** `the Schwarzschild singularity illustrates the concern, since geodesic incompleteness (LPO) feeds into the information paradox as a physical boundary condition`

Change that clause to:
```latex
the Schwarzschild singularity illustrates the concern, since geodesic incompleteness (LPO) feeds into the information paradox as if it were a physical boundary condition---though this downstream propagation has not itself been formalised
```

---

## D. LPO Formal Footnote

### D1. Add formal characterisation of LPO

**Anchor:** `Either ``all rooms are empty'' or ``here is the occupied room.''` (line 171)

After the closing `''` and before the next sentence, insert a footnote:
```latex
\footnote{Formally: for any binary sequence $\alpha : \mathbb{N} \to \{0,1\}$, either $\alpha(n) = 0$ for all $n$, or there exists $n$ with $\alpha(n) = 1$.}
```

So the line becomes:
```latex
Either ``all rooms are empty'' or ``here is the occupied room.''\footnote{Formally: for any binary sequence $\alpha : \mathbb{N} \to \{0,1\}$, either $\alpha(n) = 0$ for all $n$, or there exists $n$ with $\alpha(n) = 1$.}
```

---

## E. Act V Citations

### E1. Add bibliography entries

**Anchor:** Add these three entries in the bibliography section (between existing entries, alphabetically or at the end before `\end{thebibliography}`):

```latex
\bibitem{BoussoPolchinski2000}
R.~Bousso and J.~Polchinski,
``The string theory landscape,''
\emph{Journal of High Energy Physics} \textbf{2000}(06) (2000), 006.

\bibitem{Susskind2003}
L.~Susskind,
``The anthropic landscape of string theory,''
in \emph{Universe or Multiverse?}, ed.\ B.~Carr, Cambridge University Press, 2003.
arXiv:hep-th/0302219.

\bibitem{AMPS2013}
A.~Almheiri, D.~Marolf, J.~Polchinski, and J.~Sully,
``Black holes: complementarity vs.\ firewalls,''
\emph{Journal of High Energy Physics} \textbf{2013}(02) (2013), 062.
```

### E2. Cite in Act V text

**Anchor:** `String theory posits a landscape of $10^{500}$ vacuum states` (line 1072)

Change lines 1072–1077 to:
```latex
String theory posits a landscape of $10^{500}$ vacuum states---solutions to the equations of the theory that represent possible universes \cite{BoussoPolchinski2000, Susskind2003}.
This is an assertion about the structure of an infinite-dimensional space of solutions.
No finite experiment can probe it.
The many-worlds interpretation of quantum mechanics takes the universal wave function literally, asserting the real physical existence of a branching structure in infinite-dimensional Hilbert space.
No measurement can access the other branches.
The black hole information paradox asks what happens to quantum information at a singularity---combining two LPO-level idealizations (the singularity and the infinite-dimensional state space) into a single problem \cite{AMPS2013}.
```

---

## F. Structural Cut — "Return to the Cellar"

### F1. Trim redundant recapitulation

**Anchor:** The section begins at line 1821 with `\section{Return to the Cellar}`.

Replace everything from line 1824 (`Return to the anomalous magnetic moment`) through line 1862 (`That may be the most important thing the prediction tells us.`) with:

```latex
Return to the anomalous magnetic moment of the electron.

The number that theory and experiment agree on, to twelve decimal places, is a BISH computation.
Finite Feynman diagrams, finite integrals, finite arithmetic.
The cathedral of infinite-dimensional mathematical physics sits above this number: beautiful, useful as a thinking device, and largely idle as far as predictions are concerned.

The constructive hierarchy---developed by Brouwer for philosophical reasons, refined by Bishop \cite{Bishop1967} for mathematical reasons, and sharpened by Bridges, Ishihara \cite{Ishihara1992, Ishihara2006}, and their students into a precise instrument of logical calibration---turns out to be the right tool for mapping the boundary between the physical world and the mathematical structures we use to describe it.
It was not designed for this purpose.
That it answers questions about the foundations of physics is either a coincidence or evidence that the questions are the same question.

Whether nature is constructive is a hypothesis, not a theorem.
The evidence is machine-verified: approximately 11,000~lines of Lean~4 proofs with auditable axiom certificates across quantum mechanics, statistical mechanics, and general relativity.
The hypothesis could be wrong---a single empirical prediction that provably requires LPO would refute it.
It is stated precisely enough to be falsifiable, which is all one can ask of a scientific proposal.

We now have the tool.
The calibration table tells us where the map matches the territory and where the mapmaker's conventions begin.
What remains is finding the principle that explains why the physical world speaks the language of constructive logic, if indeed it does.

The most precise prediction in physics requires the least logical strength.
That may be the most important thing the prediction tells us.
```

This removes ~120 lines of recapitulation (HUP split, spectrum, safety diagnostic, Cubitt/MIP*, historical summary) that duplicate earlier sections with figures.

---

## G. Dedication

### G1. Add dedication

**Anchor:** After the `Statement of AI Use` section, before `\end{document}` (line 2047).

Insert:
```latex

\bigskip
\noindent\textit{For Mimi, my wife, who always knew the cellar was enough.}
```

---

## H. Gemini Review — Physics Precision Fixes

### H1. Renormalization group acknowledgment (Act IV)

The essay classifies RG fixed points as LPO+ "idle machinery" without acknowledging that Wilsonian RG is the framework that *explains why the cellar is stable* — it proves high-energy physics decouples from low-energy predictions, justifying finite-order truncation. This is a vulnerability a physicist reviewer will exploit.

**Anchor:** `The contour lines---the Feynman diagrams---are the actual geography.` (line 992)

Insert **after** that sentence:

```latex
There is an irony here that deserves acknowledgment.
The Wilsonian renormalization group---itself an LPO-level construction, since its fixed points live in an infinite-dimensional space of theories---is precisely the framework that explains \emph{why} the cellar is stable: it shows that high-energy physics decouples from low-energy predictions, justifying the truncation to finite loop order.
The cathedral's most important structural insight is the proof that the cellar is self-sufficient.
```

### H2. Yang-Mills mass gap refinement

The current text says "The physical predictions do not depend on the answer," which is too strong. If the continuum limit is trivial or conformal, that *would* contradict lattice mass generation. The claim should be about what the Millennium Problem asks for, not about whether the answer is physically irrelevant.

**Anchor:** Lines 996–998, `It is a question about the \emph{map}: whether the infinite-dimensional formalization faithfully represents the finite-dimensional physics. The physical predictions do not depend on the answer.`

Change to:

```latex
The Millennium Problem asks whether the map (continuum formalization) matches the territory (lattice computations) in a specific rigorous sense.
The lattice predictions---hadron masses, the proton charge radius---do not wait for the answer; they are already confirmed at BISH\@.
But the existence or non-existence of the continuum limit is a question about the mathematical infrastructure, not about the physical phenomena that infrastructure was built to describe.
```

---

## Summary

| Edit | Type | Lines affected | Scope |
|------|------|---------------|-------|
| A1–A2 | Build fixes | 10, 13–14 | 3 lines changed |
| B1 | Terminology | ~25 instances | Find-replace |
| C1 | Abstract scope | 39 | 1 sentence added |
| C3 | Precision | 841 | 3 words added |
| C4 | Caption | 962 | 1 line changed |
| C5 | Caption | ~1625 | 1 clause added |
| D1 | Footnote | 171 | 1 footnote added |
| E1–E2 | Citations | 1072–1077 + bib | 3 refs + 2 cites |
| F1 | Structural cut | 1824–1862 | ~120 lines removed |
| G1 | Dedication | before end | 2 lines added |
| H1 | RG acknowledgment | after 992 | 3 sentences added |
| H2 | Yang-Mills refinement | 996–998 | 3 sentences replacing 2 |

No figures need redrawing. No new sections. The paper's intellectual content is unchanged.
