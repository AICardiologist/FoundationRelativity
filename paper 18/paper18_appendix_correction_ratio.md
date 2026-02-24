# Paper 18 — Appendix A Correction: CRM vs Standard Model-Comparison

**Context:** This edit applies to the Appendix A specification (`paper18_appendix_specification.md`), specifically §A.6 (Synthesis). The issue: "compression ratio" and "input character" (continuous vs discrete parameters) are presented as CRM findings, but they are standard model-selection methodology independent of constructive mathematics. Only three observations in the appendix are genuinely CRM. The synthesis should be honest about which is which.

---

## Replace the three-observation synthesis in §A.6

Delete the current three `\paragraph` blocks ("1. Every UV approach has BISH as its core," "2. Approaches differ in input character, not logical cost," "3. The scaffolding principle produces one non-trivial UV insight") and the closing paragraph. Replace with:

```latex
Three observations emerge from the audit. The first and third are
specific to CRM; the second uses standard model-comparison
methodology included for completeness.

\paragraph{1.\ Every UV approach has $\BISH$ as its core
(CRM-specific).}
The $\LPO$, where it appears, enters through
idealizations---exact stabilization, exact gauge unification,
exact non-perturbative expansions---and is dispensable in every
case. Combined with the numerical results of
Sections~\ref{sec:phase1} and~\ref{sec:phase2}, this means the
fermion mass problem is entirely a problem within~$\BISH$, at
both the infrared and ultraviolet levels. No omniscience
principle is needed to state, derive, or verify any proposed
explanation of the mass hierarchy. This finding requires the
$\BISH$/$\LPO$ distinction to formulate and is non-trivial: it
could have been otherwise (Sumino's all-orders cancellation
mechanism for the Koide formula comes close to requiring $\LPO$
essentially). The flavor problem is a different kind of mystery
from those CRM was designed to illuminate, where $\LPO$ enters
through completed limits and its dispensability is the finding.

\paragraph{2.\ Approaches differ in compression ratio and input
character (standard methodology).}
\Cref{tab:uv_audit} also records two quantities from standard
model-comparison analysis: the \emph{compression ratio}
(observables per input parameter) and the \emph{input character}
(continuous vs.\ discrete). These do not depend on the CRM
framework---physicists routinely count parameters without
reference to constructive mathematics---but they provide useful
context for the logical audit.

The compression ratio ranges from ${<}1$ (Froggatt--Nielsen with
free $O(1)$ coefficients: more inputs than observables) to
${\sim}2.5$ ($\mathrm{SO}(10)$ for the third generation). The
input character varies: Froggatt--Nielsen and discrete flavor
symmetries use continuous parameters (flavon VEVs); string
compactification uses purely discrete parameters (flux integers,
topological data); GUTs use a mixture.

CRM sees no logical distinction between continuous and discrete
inputs evaluated to finite precision---both are $\BISH$. The
question of whether discrete inputs are ``more explained'' than
continuous ones is a question about explanatory depth, not
logical cost, and lies outside CRM's scope.

\paragraph{3.\ Exact gauge coupling unification is $\LPO$
scaffolding (CRM-specific).}
The scaffolding principle failed for the SM infrared (ten
investigations, all negative). Applied to the ultraviolet, it
identifies exact gauge coupling unification as $\LPO$ scaffolding
whose removal widens the viable GUT model space. The empirical
evidence for grand unification is approximate unification
($\BISH$): three couplings come close to meeting within
experimental error bars at ${\sim}2 \times 10^{16}$~GeV. The
assertion that they meet \emph{exactly} is a completed-infinite
statement ($\LPO$): it requires deciding equality of three real
numbers. Models achieving approximate unification without exact
unification are $\BISH$-sufficient and conventionally excluded
only because the exactness assumption is treated as a theoretical
requirement rather than an idealization.

This is a concrete instance of the scaffolding principle producing
a non-trivial observation---not solving the mass problem, but
clarifying which aspects of GUT phenomenology are empirically
grounded ($\BISH$) and which are idealizations ($\LPO$). Whether
the wider $\BISH$-sufficient model space contains new explanations
of the full mass hierarchy remains open.

\medskip
\noindent
The overall picture: CRM maps the logical geography of UV flavor
physics with precision, and the map reveals that the terrain is
uniformly $\BISH$. The interesting $\LPO$ boundaries found in
five other domains (Papers~8, 13, 14, 15, 17) do not appear here.
The one exception---exact gauge coupling unification---is not
about the mass hierarchy per se, but about the GUT framework
within which mass predictions are made. CRM's contribution to the
flavor problem is diagnostic and taxonomic: it can tell you the
logical cost of any proposed explanation, identify which
idealizations are dispensable, and flag where the scaffolding
principle has purchase. It cannot replace experiment.
```

---

## Corresponding change to the table caption

Replace the current caption of `tab:uv_audit` with:

```latex
\caption{Audit of ultraviolet approaches to the fermion mass
  hierarchy. ``Core Cost'' and ``$\LPO$ Component'' are
  CRM-specific findings. ``Cont.\ Params'' and ``Disc.\ Params''
  are standard parameter counts included for context.
  Every approach has $\BISH$ as its core logical content;
  $\LPO$ enters only through dispensable idealizations.}
```

This makes explicit, at the point of first encounter, which columns are CRM and which are conventional.

---

## No other changes required

The individual subsections (§A.1–A.5) are fine as written — they describe each approach's CRM verdict and compression ratio without overclaiming that compression ratio is itself a CRM concept. The overclaim is localized to the synthesis, and the fix above resolves it.
