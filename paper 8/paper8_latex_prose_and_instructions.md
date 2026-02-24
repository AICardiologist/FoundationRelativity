# Paper 8: Combined LaTeX — Prose Sections + Agent Instructions

## Paul C.-K. Lee, February 2026

---

# PART I: PROSE SECTIONS (Non-LaTeX, Non-Proof)

These are the written sections the agent should typeset into LaTeX.
The agent handles the mathematical proof sections (§3–4) from the
two proof drafts. The prose below covers Introduction, Discussion,
Related Work, and Bibliography.

---

## §1 INTRODUCTION (to be typeset by agent)

The thermodynamic limit is the foundational idealization of
equilibrium statistical mechanics. For a lattice system
$\Lambda \subset \mathbb{Z}^d$ with Hamiltonian $H_\Lambda$, the
free energy density $f_\Lambda(\beta) = -\frac{1}{|\Lambda|}
\log Z_\Lambda(\beta)$ is defined for each finite volume. The
thermodynamic limit asserts that $f_\infty(\beta) =
\lim_{|\Lambda| \to \infty} f_\Lambda(\beta)$ exists. Classically,
this existence follows from subadditivity and the monotone
convergence theorem: a bounded, monotone sequence of real numbers
converges.

From a constructive standpoint, the monotone convergence theorem is
not available in Bishop-style constructive mathematics (BISH). It
is equivalent over BISH to the Limited Principle of Omniscience
(LPO), which asserts that for any binary sequence $\alpha :
\mathbb{N} \to \{0,1\}$, either $\alpha(n) = 0$ for all $n$ or
there exists $n_0$ with $\alpha(n_0) = 1$. This equivalence was
established by Bridges and Vîță [BV06] as part of the systematic
classification of constructive reverse mathematics initiated by
Ishihara [Ish06] and, independently, Veldman [Vel05].

The question we address is: what is the exact logical cost of the
thermodynamic limit, and is this cost essential for the physics?

We answer both questions completely for the one-dimensional Ising
model with nearest-neighbour interactions. Our results are:

(A) **Dispensability.** For the 1D Ising chain with uniform coupling
    $J$ and inverse temperature $\beta$, we prove explicit error
    bounds $|f_N(\beta) - f_\infty(\beta)| \leq
    \frac{1}{N}\tanh(\beta)^N$ with a constructive witness $N_0$
    for any prescribed accuracy $\varepsilon > 0$. The proof is
    entirely BISH-valid — no omniscience principle is required.
    The finite-system prediction approximates the infinite-volume
    answer with computable error, and monotone convergence is
    bypassed via the closed-form transfer-matrix solution.

(B) **Calibration.** The existence of the thermodynamic limit as a
    completed real number (not merely its approximability) is
    equivalent to LPO over BISH. Specifically, we prove that
    bounded monotone convergence — instantiated through the free
    energy function $g(J) = -\log(2\cosh(\beta J))$ of the 1D
    Ising model — is equivalent to LPO via an explicit encoding
    of binary sequences into coupling sequences.

Together, these results establish that the LPO cost of the
thermodynamic limit is genuine (it is equivalent to, not merely
sufficient for, a known omniscience principle) and dispensable
(the empirical predictions require no omniscience at all).

Both results are formalized in Lean 4 with Mathlib dependencies.
The combined formalization comprises 1374 lines across 18 modules,
with zero sorries and a clean axiom profile: Part A uses no
omniscience principles whatsoever, while Part B's main theorem
`lpo_of_bmc` carries only the standard Lean metatheory axioms
(`propext`, `Classical.choice`, `Quot.sound`). The forward direction
of the LPO $\leftrightarrow$ BMC equivalence is axiomatized as
`bmc_of_lpo`, citing Bridges and Vîță [BV06].

This paper contributes to the programme of constructive reverse
mathematics applied to mathematical physics. The programme,
outlined in a companion paper [Lee26c], assigns to each physical
idealization a precise position in the constructive hierarchy:

| Physical layer | Principle | Status |
|---|---|---|
| Finite-volume Gibbs states | BISH | Trivially calibrated |
| Finite-size approximations | BISH | Part A (this paper) |
| Bidual-gap witness | $\equiv$ WLPO | Papers 2, 7 [Lee26a,b] |
| Thermodynamic limit existence | $\equiv$ LPO | Part B (this paper) |
| Spectral gap decidability | Undecidable | Cubitt et al. [CPW15] |

Our results calibrate two rows of this table, upgrading them from
"route-costed" to "formally verified."


## §2 PRELIMINARIES (brief — agent fills in from proof drafts)

Agent should typeset: BISH definition, LPO/WLPO/LLPO hierarchy,
BMC definition, 1D Ising setup (Hamiltonian, transfer matrix,
eigenvalues, partition function), free energy definitions. Draw
from Part A proof draft §1–2.


## §5 SYNTHESIS AND DISCUSSION (to be typeset by agent)

### 5.1 The dispensability–calibration conjunction

Neither Part A nor Part B says much in isolation. Part A alone is a
calculation: the 1D Ising model has a closed-form solution, so of
course finite-size bounds are elementary. Part B alone is an
instantiation of a known equivalence: BMC $\leftrightarrow$ LPO is
Bridges–Vîță, and dressing it in Ising clothing does not change the
abstract content. The force of the paper lies in the conjunction.

Part B establishes that the monotone-convergence route to the
thermodynamic limit genuinely costs LPO — the cost is not an
artefact of a particular proof strategy but an intrinsic feature of
the limit assertion. Part A then shows that this cost is
dispensable for empirical predictions: the finite-system prediction
$f_N(\beta)$ approximates $f_\infty(\beta)$ within $\varepsilon$
for constructively computable $N_0$, and the proof uses nothing
beyond BISH. The pattern is: the idealization costs omniscience;
the empirical content does not.

This pattern is precisely what the logical geography hypothesis
[Lee26c] predicts. The 1D Ising model is the first complete test
case — the simplest model where the dispensability question is
nontrivial and verifiable.

### 5.2 Relation to the phase-transition debate

The philosophical literature on the "paradox of phase transitions"
— the apparent indispensability of infinite idealizations for
explaining phase transitions in finite systems — has been active
for two decades. Batterman [Bat02, Bat05] argued that infinite
limits play an essential and irreducible explanatory role.
Butterfield [But11] and Callender [Cal01] pushed back, arguing
that finite-system approximations suffice for physical predictions
even if the mathematical apparatus of the thermodynamic limit is
explanatorily convenient. Van Wierst [vW19] explored the
consequences of adopting constructive mathematics for the phase
transition framework, arguing that constructive mathematics forces
"de-idealizations" of standard statistical-mechanical theories.

Our results make this debate precise in one model. The
thermodynamic limit is not merely "convenient" — it has a precise
logical cost (LPO), and this cost is not an artefact of the proof
but an equivalence. At the same time, the limit is genuinely
dispensable for predictions: the finite-size error bound is
BISH-provable. The 1D Ising model, admittedly, does not exhibit
phase transitions, so our dispensability result does not directly
address the paradox as stated (which concerns the necessity of
infinite limits for explaining phase transitions). But it does
establish the methodology: for each physical layer, determine the
exact logical cost and then ask whether the empirical content can
be recovered at a lower cost.

### 5.3 The encoding objection

A natural objection to Part B is that the encoding of binary
sequences into coupling sequences — and the subsequent application
of the free energy function $g(J) = -\log(2\cosh(\beta J))$ — is
merely bounded monotone convergence in disguise. The encoded
sequence $F(N) \in \{g(J_0), g(J_1)\}$ is a $\{0,1\}$-valued
monotone sequence composed with a strictly decreasing function, and
the decision procedure is just the abstract BMC $\to$ LPO proof
applied to this specific case.

This objection is mathematically correct and interpretively
irrelevant. The abstract equivalence BMC $\leftrightarrow$ LPO is
known from [BV06]. The contribution of Part B is not a new theorem
in constructive reverse mathematics but a verified observation
that BMC, when instantiated through the 1D Ising free energy,
*is* the assertion that the thermodynamic limit exists. The
formalization makes explicit what the mathematical prose leaves
implicit: the encoding is BISH-valid, the gap $\delta = g(J_0) -
g(J_1) > 0$ is constructively positive, and the witness extraction
works without hidden omniscience. The Lean axiom audit confirms
this.

This is the same methodological move as [Lee26a], where the
abstract equivalence between WLPO and $\neg\neg$-stable
decidability was known from Ishihara and Diener, and the
contribution was the specific Banach-space instantiation and the
machine verification.

### 5.4 Limitations and future directions

The 1D Ising model is the simplest nontrivial lattice model, and
our results exploit its complete solvability. The key open
questions are:

(i) **Higher dimensions.** The 2D Ising model (Onsager solution)
    has a phase transition. Does the finite-size error bound remain
    BISH-provable? The Onsager solution involves elliptic integrals,
    whose constructive status requires investigation.

(ii) **General Hamiltonians.** For translation-invariant,
     finite-range Hamiltonians on $\mathbb{Z}^d$, the
     thermodynamic limit exists classically by subadditivity. Is
     the existence always LPO-equivalent, or does it depend on the
     Hamiltonian?

(iii) **Ineliminability.** An ineliminability result — showing that
      any constructive proof of free energy convergence for a
      specific model must use BMC — would be a genuinely new
      contribution to constructive reverse mathematics. This is an
      open problem beyond the scope of the present paper.


## §6 LEAN 4 FORMALIZATION (to be typeset by agent)

### 6.1 Module structure

The formalization is organized as a single Lean 4 project with
two parts sharing common infrastructure.

**Part A (BISH dispensability, 729 lines, 10 modules):**
Basic.lean, EigenvalueProps.lean, LogBounds.lean,
TransferMatrix.lean, PartitionTrace.lean,
FreeEnergyDecomp.lean, ErrorBound.lean, ComputeN0.lean,
Main.lean, SmokeTest.lean.

**Part B (LPO calibration, 644 lines, 8 modules):**
PartB_Defs.lean, PartB_RunMax.lean, PartB_FreeEnergyAnti.lean,
PartB_CouplingSeq.lean, PartB_EncodedSeq.lean,
PartB_Forward.lean, PartB_Backward.lean, PartB_Main.lean.

**Combined:** 1374 lines, 18 modules, 0 sorries.

### 6.2 Axiom audit

```
-- Part A main theorem:
#print axioms Papers.P8.ising_1d_dispensability
-- [propext, Classical.choice, Quot.sound]
-- No LPO, WLPO, LLPO, or custom axioms.

-- Part B backward direction:
#print axioms lpo_of_bmc
-- [propext, Classical.choice, Quot.sound]
-- BMC appears as a hypothesis, not an axiom.

-- Part B equivalence:
#print axioms lpo_iff_bmc
-- [propext, Classical.choice, Quot.sound, bmc_of_lpo]
-- bmc_of_lpo is a cited axiom (Bridges–Vîță 2006).
```

The Part A audit confirms that the BISH dispensability proof uses
no omniscience principles. `Classical.choice` is the ambient Lean
metatheory, not an object-level axiom. The Part B audit shows that
the novel content (backward direction) is fully proved, while the
forward direction is axiomatized with citation.

### 6.3 Design decisions

**Option 3 for $Z_N$.** The partition function $Z_N$ is defined
directly as $\lambda_+^N + \lambda_-^N$ (the eigenvalue formula).
The classical identity $Z_N = \operatorname{Tr}(T^N) = \sum_\sigma
\exp(-\beta H_N(\sigma))$ is provided as a bonus lemma
(`PartitionTrace.lean`) connecting the definition to the transfer
matrix, but is not used in either Part A or Part B. The heavier
direction (configuration sum $= \operatorname{Tr}(T^N)$) is
documented in the paper but omitted from the formalization. This
keeps the axiom profile clean without bridge axioms.

**`bmc_of_lpo` axiom.** The forward direction (LPO $\to$ BMC) is
axiomatized, following the same pattern as `ell1_not_reflexive`
in [Lee26b]. The novel content of the paper is the backward
direction and the physical instantiation. A complete formalization
of the forward direction is an elimination target for future work.


## BIBLIOGRAPHY

```bibtex
@book{BV06,
  author    = {Douglas S. Bridges and Lumini\c{t}a Simona V\^{i}\c{t}\u{a}},
  title     = {Techniques of Constructive Analysis},
  series    = {Universitext},
  publisher = {Springer},
  address   = {New York},
  year      = {2006},
  doi       = {10.1007/978-0-387-38147-3}
}

@book{Bis67,
  author    = {Errett Bishop},
  title     = {Foundations of Constructive Analysis},
  publisher = {McGraw-Hill},
  address   = {New York},
  year      = {1967}
}

@book{BB85,
  author    = {Errett Bishop and Douglas Bridges},
  title     = {Constructive Analysis},
  series    = {Grundlehren der mathematischen Wissenschaften},
  volume    = {279},
  publisher = {Springer},
  address   = {Berlin},
  year      = {1985}
}

@incollection{Ish05,
  author    = {Hajime Ishihara},
  title     = {Constructive reverse mathematics: compactness properties},
  booktitle = {From Sets and Types to Topology and Analysis},
  editor    = {Laura Crosilla and Peter Schuster},
  series    = {Oxford Logic Guides},
  volume    = {48},
  pages     = {245--267},
  publisher = {Oxford University Press},
  year      = {2005}
}

@article{Ish06,
  author  = {Hajime Ishihara},
  title   = {Reverse mathematics in {Bishop's} constructive mathematics},
  journal = {Philosophia Scientiae, Cahier Sp\'{e}cial},
  volume  = {6},
  pages   = {43--59},
  year    = {2006},
  doi     = {10.4000/philosophiascientiae.406}
}

@article{Ish90,
  author  = {Hajime Ishihara},
  title   = {An omniscience principle, the {K\"{o}nig} lemma and the {Hahn--Banach} theorem},
  journal = {Zeitschrift f\"{u}r Mathematische Logik und Grundlagen der Mathematik},
  volume  = {36},
  pages   = {237--240},
  year    = {1990}
}

@phdthesis{Die18,
  author  = {Hannes Diener},
  title   = {Constructive Reverse Mathematics},
  school  = {Universit\"{a}t Siegen},
  year    = {2018},
  note    = {Habilitationsschrift. arXiv:1804.05495}
}

@article{Man88,
  author  = {Mark Mandelkern},
  title   = {Limited omniscience and the {Bolzano--Weierstrass} principle},
  journal = {Bulletin of the London Mathematical Society},
  volume  = {20},
  pages   = {319--320},
  year    = {1988}
}

@article{CPW15,
  author  = {Toby S. Cubitt and David Perez-Garcia and Michael M. Wolf},
  title   = {Undecidability of the spectral gap},
  journal = {Nature},
  volume  = {528},
  pages   = {207--211},
  year    = {2015},
  doi     = {10.1038/nature16059}
}

@article{vW19,
  author  = {Pauline van Wierst},
  title   = {The paradox of phase transitions in the light of constructive mathematics},
  journal = {Synthese},
  volume  = {196},
  number  = {5},
  pages   = {1863--1884},
  year    = {2019},
  doi     = {10.1007/s11229-017-1637-z}
}

@book{Bat02,
  author    = {Robert W. Batterman},
  title     = {The Devil in the Details: Asymptotic Reasoning in Explanation, Reduction, and Emergence},
  publisher = {Oxford University Press},
  address   = {New York},
  year      = {2002}
}

@article{Bat05,
  author  = {Robert W. Batterman},
  title   = {Critical phenomena and breaking drops: Infinite idealizations in physics},
  journal = {Studies in History and Philosophy of Modern Physics},
  volume  = {36},
  pages   = {225--244},
  year    = {2005}
}

@article{But11,
  author  = {Jeremy Butterfield},
  title   = {Less is Different: Emergence and Reduction Reconciled},
  journal = {Foundations of Physics},
  volume  = {41},
  number  = {6},
  pages   = {1065--1135},
  year    = {2011}
}

@article{Cal01,
  author  = {Craig Callender},
  title   = {Taking Thermodynamics Too Seriously},
  journal = {Studies in History and Philosophy of Science Part B},
  volume  = {32},
  number  = {4},
  pages   = {539--553},
  year    = {2001}
}

@article{She13,
  author  = {Elay Shech},
  title   = {What is the Paradox of Phase Transitions?},
  journal = {Philosophy of Science},
  volume  = {80},
  number  = {5},
  pages   = {1170--1181},
  year    = {2013}
}

@incollection{MC13,
  author    = {Tarun Menon and Craig Callender},
  title     = {Turn and Face the Strange\ldots{} Ch-ch-changes: Philosophical Questions Raised by Phase Transitions},
  booktitle = {The Oxford Handbook of Philosophy of Physics},
  editor    = {Robert Batterman},
  publisher = {Oxford University Press},
  year      = {2013},
  pages     = {189--223}
}

@article{FPRRS19,
  author  = {Samuel C. Fletcher and Patricia Palacios and Laura Ruetsche and Elay Shech},
  title   = {Infinite idealizations in science: an introduction},
  journal = {Synthese},
  volume  = {196},
  number  = {5},
  pages   = {1657--1669},
  year    = {2019}
}

@book{Rue99,
  author    = {David Ruelle},
  title     = {Statistical Mechanics: Rigorous Results},
  publisher = {Imperial College Press},
  address   = {London},
  year      = {1999},
  note      = {Reprint of the 1969 edition}
}

@book{Sim09,
  author    = {Stephen G. Simpson},
  title     = {Subsystems of Second Order Arithmetic},
  edition   = {2nd},
  publisher = {Cambridge University Press},
  year      = {2009}
}

@misc{Lee26a,
  author = {Paul C.-K. Lee},
  title  = {{WLPO} equivalence of the bidual gap in $\ell^1$: a {Lean 4} formalization},
  year   = {2026},
  note   = {Paper 2 in the constructive reverse mathematics series}
}

@misc{Lee26b,
  author = {Paul C.-K. Lee},
  title  = {Non-reflexivity of $S_1(H)$ implies {WLPO}: a {Lean 4} formalization},
  year   = {2026},
  note   = {Paper 7 in the constructive reverse mathematics series}
}

@misc{Lee26c,
  author = {Paul C.-K. Lee},
  title  = {A logical geography of physical idealizations},
  year   = {2026},
  note   = {Logical geography synthesis paper}
}

@book{Bax82,
  author    = {Rodney J. Baxter},
  title     = {Exactly Solved Models in Statistical Mechanics},
  publisher = {Academic Press},
  address   = {London},
  year      = {1982}
}

@article{Ons44,
  author  = {Lars Onsager},
  title   = {Crystal statistics. {I.} A two-dimensional model with an order-disorder transition},
  journal = {Physical Review},
  volume  = {65},
  pages   = {117--149},
  year    = {1944}
}
```

---

# PART II: AGENT INSTRUCTIONS FOR LATEX COMPILATION

---

## OVERVIEW

You are writing the LaTeX for Paper 8 in Paul C.-K. Lee's
constructive reverse mathematics series. The paper combines two
results — Part A (BISH dispensability of the 1D Ising finite-size
bounds) and Part B (LPO equivalence of bounded monotone convergence
instantiated through the free energy) — into a single paper with a
unified Lean 4 formalization.

**Mirror the structure and style of Paper 7** (`paper-v6-020526.tex`
or equivalent), which proved that non-reflexivity of $S_1(H)$
implies WLPO. In particular:

1. Same documentclass, package set, theorem environments, notation
   macros, and \leanok / \leanpartial status indicators as Paper 7.
2. Same BibTeX style.
3. Same level of proof detail in the mathematical sections.
4. Same "Lean Formalization" section structure at the end.

## FILES YOU HAVE

1. `paper8_1d_ising_proof_draft.md` — Part A proof draft (634 lines).
   Contains: 1D Ising setup, eigenvalue computation, free energy
   decomposition, error bound, constructive $N_0$ witness, Lean
   signatures. This is §3 of the paper.

2. `paper8_partB_proof_draft.md` — Part B proof draft (≈500 lines).
   Contains: LPO/BMC definitions, running maximum encoding,
   coupling sequence, gap lemma, decision procedure, witness
   extraction, Lean signatures. This is §4 of the paper.

3. This file (Part I above) — Introduction, Discussion,
   Bibliography. These are §1, §5, §6.

## PAPER STRUCTURE

```
\title{The Logical Cost of the Thermodynamic Limit:\\
       LPO-Equivalence and BISH-Dispensability\\
       for the 1D Ising Free Energy}
\subtitle{A Lean 4 Formalization}
\author{Paul C.-K. Lee}
```

### Section plan:

§1. Introduction
    — Use the prose from Part I §1 above, verbatim or lightly
      edited for LaTeX. Include the calibration table.
    — End with paper outline paragraph.

§2. Preliminaries
    — 2.1 Constructive frameworks (BISH, LPO, WLPO, BMC).
      Copy definitions from Part B proof draft §1.
    — 2.2 The 1D Ising model (Hamiltonian, transfer matrix,
      eigenvalues, partition function, free energy).
      Copy from Part A proof draft §1.
    — 2.3 The function $g(J) = -\log(2\cosh(\beta J))$.
      Copy from Part B proof draft §2.

§3. Part A: BISH Dispensability
    — 3.1 Free energy decomposition (from Part A §3)
    — 3.2 The error bound (from Part A §4)
    — 3.3 Constructive $N_0$ witness (from Part A §5)
    — 3.4 The dispensability theorem (from Part A §6)
    — Mark all theorems and lemmas with \leanok.

§4. Part B: LPO Calibration
    — 4.1 Forward direction: LPO → BMC → convergence
      (brief, citing [BV06])
    — 4.2 The encoding (running maximum, coupling sequence,
      free energy sequence — from Part B §4.1)
    — 4.3 The decision procedure (from Part B §§4.3–4.4)
    — 4.4 Witness extraction (from Part B §4.6)
    — 4.5 The equivalence theorem (from Part B §5)
    — Mark theorems with \leanok. Mark bmc_of_lpo with
      \leanpartial and note "[Bridges–Vîță 2006], axiomatized."

§5. Discussion
    — Use the prose from Part I §5 above.
    — 5.1 The dispensability–calibration conjunction
    — 5.2 Relation to the phase-transition debate
    — 5.3 The encoding objection
    — 5.4 Limitations and future directions

§6. Lean 4 Formalization
    — Use the content from Part I §6 above.
    — 6.1 Module structure (table of all 18 modules)
    — 6.2 Axiom audit (verbatim #print axioms output)
    — 6.3 Design decisions (Option 3, bmc_of_lpo axiom)

References
    — Use the BibTeX from Part I above.

## STYLE REQUIREMENTS

1. **No bullet points or numbered lists in prose.** Write in
   paragraphs. The only tables are the calibration table (§1, §5)
   and the module structure table (§6).

2. **Theorem environments.** Use theorem, lemma, proposition,
   definition, remark. Number within sections.

3. **Status indicators.** Every theorem/lemma that is formalized
   gets \leanok after its label. Axiomatized results get
   \leanpartial. Example:
   ```
   \begin{theorem}[Dispensability] \leanok
   ```

4. **Lean code listings.** Use lstlisting with the lean style
   from Paper 7. Include the main theorem signatures from each
   proof draft. Do NOT include full proofs in Lean — only
   signatures and #print axioms output.

5. **Cross-references.** Refer to Part A as "Part A (§3)" and
   Part B as "Part B (§4)" throughout.

6. **Notation.** $f_N$ for finite-volume free energy, $f_\infty$
   for infinite-volume, $\lambda_+, \lambda_-$ for eigenvalues,
   $r = \tanh(\beta)$ for the ratio, $g(J)$ for the free energy
   at coupling $J$, $\delta$ for the gap $g(J_0) - g(J_1)$.

7. **Page count target.** 20–25 pages including references.

## CRITICAL INSTRUCTIONS

- The mathematical content in §3 and §4 is COMPLETE in the two
  proof drafts. Typeset it faithfully. Do not simplify or
  abbreviate the proofs.

- The "Constructive note" paragraphs in the proof drafts should
  become \begin{remark} environments in the LaTeX.

- Include the Appendix on elementary inequalities from Part A
  draft (A1, A2, A3) as an appendix.

- The title, abstract, and introduction should make clear that
  this is one paper with two complementary results, not a
  compilation of two separate results.

## ABSTRACT (for agent to typeset)

We prove two complementary results about the thermodynamic limit
of the one-dimensional Ising model, formalized in Lean 4.
(A) The finite-size error bound
$|f_N(\beta) - f_\infty(\beta)| \leq \frac{1}{N}\tanh(\beta)^N$
is provable in Bishop-style constructive mathematics (BISH)
without any omniscience principle. A constructive witness $N_0$
for any prescribed accuracy $\varepsilon > 0$ is explicitly
computed. (B) The existence of the thermodynamic limit as a
completed real number is equivalent over BISH to the Limited
Principle of Omniscience (LPO), via the known equivalence between
LPO and bounded monotone convergence instantiated through the
Ising free energy function. Together, these results establish that
the LPO cost of the thermodynamic limit is genuine and
dispensable: the idealization costs exactly LPO, but the empirical
content requires no omniscience. The combined formalization
comprises 1374 lines of Lean 4 across 18 modules with zero
sorries.
