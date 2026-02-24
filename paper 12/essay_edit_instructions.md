# Edit Instructions for essay_constructive_history.tex (Paper 12)
# ================================================================
#
# These are four edits to the essay, adding ~20 sentences of
# interpretive material. No structural changes. No new sections.
# The LaTeX file is at: essay_constructive_history.tex
#
# IMPORTANT: Make edits in reverse order (Edit 4 first, Edit 1 last)
# to preserve line numbers. Or use unique anchor strings for each edit.
#
# ================================================================

## EDIT 2: Born Rule Paragraph
## Location: AFTER the line ending "infinite measurement sequences."
## Anchor string (unique): "The classical overhead enters only when you extract statistical information from infinite measurement sequences."
## Action: INSERT the following paragraph AFTER that line (after line 524), with a blank line before and after.

INSERT AFTER "The classical overhead enters only when you extract statistical information from infinite measurement sequences.":

```latex
This separation has a deeper significance than a technical footnote about choice principles.
The Born rule---the postulate that measurement probabilities equal $|\langle\lambda|\psi\rangle|^2$---is itself an idealization.
It asserts that relative frequencies over infinitely many measurements converge to definite probabilities; that convergence is where Dependent Choice enters.
The geometric content of quantum mechanics---that a single state cannot be simultaneously sharp in non-commuting observables---is BISH, a property of one vector in a finite-dimensional Hilbert space requiring no measurements at all.
The statistical content---that repeated measurements yield frequencies approaching the Born probabilities---requires the construction of infinite measurement sequences and the extraction of their limits.
Quantum mechanics thus splits into two logical layers: a constructive geometric core (preparation uncertainty, Cauchy--Schwarz, BISH) and a statistical superstructure (measurement uncertainty, the Born rule, Dependent Choice).
The physical core that makes quantum mechanics \emph{strange}---superposition, interference, non-commutativity---needs no idealization.
The apparatus that makes quantum mechanics \emph{predictive} over infinite ensembles does.
```

## EDIT 1: Spectrum Paragraph + Unifying Observation
## Location: AFTER the line "The most distinctively quantum phenomenon needs the least logical strength."
## Anchor string (unique): "The most distinctively quantum phenomenon needs the least logical strength."
## Action: INSERT the following two paragraphs AFTER that line (after line 548), with a blank line before and after.

INSERT AFTER "The most distinctively quantum phenomenon needs the least logical strength.":

```latex
The spectrum itself---the central mathematical object of quantum mechanics, the set of possible measurement outcomes for an observable---is an idealization.
An experimentalist measures finitely many energy levels to finite precision: the hydrogen Lyman series, a handful of absorption lines, each located within instrumental error bars.
That is BISH\@.
The assertion that a specific value $\lambda$ belongs \emph{exactly} to the spectrum of an operator~$H$---rather than merely within~$\varepsilon$ of the spectrum for every~$\varepsilon > 0$---requires Markov's Principle \cite{Lee2026f}.
The full spectral theorem, guaranteeing a complete projection-valued measure decomposing any self-adjoint operator into spectral subspaces, requires substantially more.
The most fundamental mathematical structure of quantum mechanics---the object from which every measurement prediction flows---has a precisely calibrated logical cost, and the physical content accessible to a finite observer sits below that cost at BISH\@.

Taken together, the quantum calibrations reveal a layered architecture.
Von~Neumann's 1932 formalization introduced not one but three measurable layers of idealization above BISH: the Born rule's convergence of measurement statistics (Dependent Choice, \cite{Lee2026g}), exact spectral membership (Markov's Principle, \cite{Lee2026f}), and the existence of singular states in the bidual (WLPO, \cite{Lee2026a}).
Each layer has a machine-verified logical cost.
Each separates physical content from mathematical infrastructure.
The pattern is uniform: what a finite observer can prepare, measure, and record is BISH; each assertion about completed infinities---infinite measurement sequences, exact set membership, functionals on infinite-dimensional duals---costs a specific, independently identifiable non-constructive principle.
```

## EDIT 4: Cubitt/MIP* = RE Remark (expanded)
## Location: REPLACE the existing paragraph at lines 991-996.
## Anchor string: The block starting with "\textbf{Beyond the summit (undecidable).}" and ending with "conflating them would misrepresent both."
## Action: REPLACE that entire block (lines 991-996) with the expanded version below.

REPLACE the block:
```
\textbf{Beyond the summit (undecidable).}
The spectral gap problem---whether the Hamiltonian of an infinite lattice system has a gap above the ground state energy---is undecidable in the sense of Turing: no algorithm can determine the answer from the Hamiltonian's local interaction rules \cite{Cubitt2015}.
This is not ``a level above LEM'' in the logical hierarchy; it is an orthogonal phenomenon.
LEM does not help you compute an uncomputable function.
Undecidability means that the idealization strategy hits a different kind of ceiling---not insufficient logical strength, but the inherent limitation of algorithmic procedures applied to infinite lattice systems.
The summit of the omniscience hierarchy (LPO) and Turing undecidability are distinct obstructions, and conflating them would misrepresent both.
```

WITH:
```latex
\textbf{Beyond the summit (undecidable).}
The spectral gap problem---whether the Hamiltonian of an infinite lattice system has a gap above the ground state energy---is undecidable in the sense of Turing: no algorithm can determine the answer from the Hamiltonian's local interaction rules \cite{Cubitt2015}.
This is not ``a level above LEM'' in the logical hierarchy; it is an orthogonal phenomenon.
LEM does not help you compute an uncomputable function.
Undecidability means that the idealization strategy hits a different kind of ceiling---not insufficient logical strength, but the inherent limitation of algorithmic procedures applied to infinite lattice systems.
The summit of the omniscience hierarchy (LPO) and Turing undecidability are distinct obstructions, and conflating them would misrepresent both.

Yet the two hierarchies share a common boundary.
For any \emph{finite} lattice, the spectral gap is a computable real number---eigenvalues of a finite Hermitian matrix are BISH, and the question ``is the gap above~$\varepsilon$?'' is decidable by rational approximation.
The undecidability of Cubitt et~al.\ enters only through the thermodynamic limit $N \to \infty$---the same limit that costs LPO in the Ising calibration.
The constructive hierarchy and the computability hierarchy are orthogonal axes, but they agree on where the physics--formalism boundary falls: finite systems sit at BISH/decidable, and infinite idealizations sit above BISH in both.
A similar pattern appears in the foundations of quantum correlations.
The set of correlations achievable by finite-dimensional quantum systems is identical whether formalized via tensor products or commuting operators, and the Tsirelson bound $2\sqrt{2}$ holds in both formalizations at BISH \cite{Lee2026paper11}.
Ji, Natarajan, Vidick, Wright, and Yuen showed that this equivalence fails catastrophically in infinite dimensions: the membership problem for infinite-dimensional commuting-operator correlations is RE-complete---as hard as the halting problem \cite{JNVWY2021}.
The physical correlations, preparable with finite entanglement and measurable by finite apparatus, are BISH and formalization-invariant.
The mathematical excess---correlations requiring infinite entanglement in infinite-dimensional spaces---is where the formalizations diverge, and the divergence reaches the highest levels of the computability hierarchy.
Neither result has been calibrated against the omniscience hierarchy (that would require proving specific equivalences with WLPO, LPO, or higher principles, which remains open), but both confirm the programme's central pattern: physical content at BISH, with logical cost increasing monotonically as the formalism extends beyond the finite.
```

## EDIT 5: Add bibliography entry for Ji et al. (MIP* = RE)
## Location: In the bibliography section, AFTER the \bibitem{Ishihara2006} entry.
## Find a suitable alphabetical location near "J" entries. Insert after any "I" entries.
## Anchor: Find the bibliography and insert in alphabetical order after entries starting with "I".

First, find where "I" entries end and "K" or later entries begin. The Cubitt entry is at line 1318. Look for entries near alphabetical position "J".

FIND the entry for \bibitem{Gisin2020} (which starts around line 1338) and INSERT BEFORE it:

```latex
\bibitem{JNVWY2021}
Z.~Ji, A.~Natarajan, T.~Vidick, J.~Wright, and H.~Yuen,
``{MIP}$^*$ = {RE},''
\emph{Communications of the ACM} \textbf{64}(11) (2021), 131--138.

```

# ================================================================
# SUMMARY OF CHANGES
# ================================================================
#
# Edit 1: ~11 lines inserted after line 548 (spectrum + unifying paragraph)
# Edit 2: ~8 lines inserted after line 524 (Born rule paragraph)
# Edit 4: ~10 lines added to existing Cubitt paragraph (lines 991-996 replaced with expanded version)
# Edit 5: 4 lines added to bibliography (Ji et al. reference)
#
# Total: ~33 lines of new LaTeX content
# No sections added or removed
# No figures changed
# No equations added
# No existing content deleted (Edit 4 preserves all original sentences)
#
# VERIFICATION: After edits, search for these strings to confirm:
# - "The Born rule---the postulate" (Edit 2 present)
# - "The spectrum itself---the central mathematical object" (Edit 1 present)
# - "Von~Neumann's 1932 formalization introduced not one but three" (Edit 1 present)
# - "Ji, Natarajan, Vidick, Wright, and Yuen" (Edit 4 present)
# - "JNVWY2021" (Edit 5 present)
# - All original content from lines 991-996 still present (Edit 4 preserves it)
