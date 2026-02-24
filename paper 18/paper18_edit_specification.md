# Paper 18 — Edit Specification for Combined Phase 1 + Phase 2 Technical Note

**Input:** `paper18_writeup.tex` (current Phase 1 only)  
**Output:** `paper18_writeup_v2.tex` (combined Phase 1 + Phase 2)  
**Goal:** Integrate the Phase 2 results (five additional investigations, all negative) into a unified technical note that tells the complete story: hypothesis, scaffolding principle, systematic test across ten investigations, definitive negative, scope finding.

---

## Overall Structure Change

The current paper has this structure:

```
1. Introduction
2. The Computation (beta functions, discrete map)
3. Results (QFP, discrete vs continuous, hierarchy, secondary)
4. Discussion (diagnostic not generative, BISH-only domain, CRM analysis of approaches)
5. Conclusion
```

The new paper should have:

```
1. Introduction (expanded — include the scaffolding principle)
2. The Scaffolding Hypothesis (NEW — the intellectual core)
3. The Standard Model Yukawa System (moved/condensed from old §2)
4. Phase 1: One-Loop Discrete Map (old §3, lightly edited)
5. Phase 2: Five Additional Tests (NEW — the five investigations)
6. Discussion (substantially rewritten)
7. Conclusion (rewritten)
```

The title should change to reflect the expanded scope:

**New title:**
```latex
\title{%
  \textbf{The Scaffolding Principle and the Fermion Mass Hierarchy:\\[4pt]
  Ten Numerical Tests of CRM as a Generative Methodology}\\[6pt]
  {\normalsize Technical Note~18 in the Constructive Reverse Mathematics Series}%
}
```

The abstract needs a full rewrite. Here is the new abstract:

```latex
\begin{abstract}
The constructive reverse mathematics (CRM) programme has established,
across five physics domains, that the passage from finite computation
($\BISH$) to completed infinite limit costs $\LPO$ via Bounded
Monotone Convergence. This pattern suggests a \emph{scaffolding
principle}: when physicists use $\LPO$-level idealizations (exact
symmetries, all-orders results, continuous limits), the idealizations
may constrain the architecture of explanations, and removing them may
reveal $\BISH$-level mechanisms invisible in the conventional
formalism. We test this principle on the fermion mass hierarchy---one
of the deepest open problems in particle physics---through ten
numerical investigations spanning two phases: one-loop and two-loop
beta functions, small and large step-size discrete maps, individual
and ratio-space couplings, smooth and threshold-corrected running,
and standard and circulant (Koide) parameterizations. All ten
investigations yield negative results. The Standard Model's infrared
dynamics do not determine the mass hierarchy in any parameterization,
at any loop order, or at any discretization scale tested. CRM is a
powerful diagnostic framework; its generative capacity, at least for
the flavor problem, is null. The investigation establishes the first
domain in the CRM series where the entire computation is $\BISH$
with no $\LPO$ boundary, confirming that $\LPO$ enters physics
through completed limits and nowhere else.
\end{abstract}
```

---

## Section-by-Section Specification

### §1 Introduction

Keep the first two paragraphs (lines 130–152) essentially as they are — the CRM background and five-domain pattern. Then replace the third paragraph (lines 154–163) with an expanded version that introduces the scaffolding principle and the generative question:

```latex
This pattern generates two predictions. First, in domains where no
completed limit is needed, the entire computation should be $\BISH$,
with no $\LPO$ boundary. Second---and more ambitiously---the
distinction between $\BISH$ and $\LPO$ might be
\emph{generative}: stripping $\LPO$ scaffolding from physics
might reveal mechanisms invisible in the conventional formalism.

We test both predictions on the Standard Model Yukawa
renormalization group. The beta functions, evaluated as a discrete
finite-step map, provide a natural $\BISH$-complete domain for the
first prediction. For the second, the fermion mass
hierarchy---thirteen free Yukawa parameters spanning six orders of
magnitude with no known explanation---provides a test case where
new mechanisms would be physically significant. We report ten
numerical investigations across two phases, systematically testing
whether the mass hierarchy emerges from the SM's infrared dynamics
when analyzed through the CRM lens.
```

### §2 The Scaffolding Hypothesis (NEW SECTION)

This is the intellectual core of the paper — the idea that motivated the investigation. Insert after the Introduction:

```latex
\section{The Scaffolding Hypothesis}\label{sec:scaffolding}

\subsection{LPO Idealizations as Architectural Constraints}

When a physicist invokes an $\LPO$-level idealization---an exact
symmetry, an all-orders perturbative result, a continuous
limit---the idealization does not merely extend a result to infinite
precision. It \emph{constrains the architecture of the explanation}.
Only mechanisms compatible with the idealization are considered;
mechanisms that achieve the same finite-precision result by other
means are excluded from the search space.

\subsection{The Sumino Example}

The observation that motivated this investigation comes from Koide's
charged lepton mass formula~\cite{Koide1983}:
\begin{equation}\label{eq:koide}
  Q = \frac{m_e + m_\mu + m_\tau}
    {(\sqrt{m_e} + \sqrt{m_\mu} + \sqrt{m_\tau})^2}
    = \frac{2}{3},
\end{equation}
satisfied to ${\sim}10^{-5}$ precision. Sumino~\cite{Sumino2009}
explains this by postulating a $\mathrm{U}(3) \times \mathrm{SU}(2)$
family gauge symmetry whose radiative corrections cancel QED
corrections to \emph{all orders} in perturbation theory, preserving
$Q = \text{exactly}~2/3$ at every energy scale. This all-orders
cancellation is an $\LPO$ statement---a completed infinite assertion
that cannot be verified at finitely many loop orders.

The CRM-informed question is different: \emph{why is $Q = 2/3$ to
$10^{-5}$ precision at the loop orders we can compute?} This is a
$\BISH$ question. It does not require an exact gauge symmetry or
all-orders cancellation. It admits a larger space of potential
mechanisms---finite-order algebraic structures, approximate
cancellations, dynamical attractors in the RG flow---that are
excluded by the demand for $\LPO$-level exactness.

\subsection{The General Principle}

More broadly: the standard treatment of the renormalization group
as a continuous flow (an ODE with solutions defined by limits of
Riemann sums) is an $\LPO$ idealization. The $\BISH$ content is
the discrete map at finite step count. Physicists search for exact
infrared fixed points of the continuous flow. But the physically
relevant question may be: what structure exists in the \emph{finite
discrete map}? Fixed points of the continuous flow are necessarily
fixed points of the discrete map, but the converse need not hold.
The discrete map could exhibit quasi-fixed-point structure, ratio-space
attractors, or threshold-driven self-consistency conditions invisible
in the continuous limit.

We call this the \textbf{scaffolding principle}: $\LPO$ idealizations
serve as scaffolding for physical explanations; removing them may
reveal the $\BISH$ structure underneath, which may differ from what
the scaffolding suggests. The fermion mass hierarchy provides a
concrete test.
```

### §3 The Standard Model Yukawa System

This is the old §2 (lines 167–218), essentially unchanged. Rename the section header and keep the beta functions and physical constants. No substantive edits needed except:

- Change section number references if any exist
- Add a sentence at the end noting that Phase 2 also uses two-loop gauge beta functions (give the coefficients or cite Luo-Wang-Xiao)

### §4 Phase 1: One-Loop Discrete Map

This is the old §3 (Results), lines 222–319, essentially unchanged. Rename to "Phase 1" and add a brief preamble:

```latex
\section{Phase~1: One-Loop Discrete Map}\label{sec:phase1}

Phase~1 tests the narrowest version of the scaffolding
hypothesis: whether the one-loop SM beta functions, treated as a
discrete RK4 map with small step size, contain attractor structure
that produces the mass hierarchy from generic initial conditions.
Five questions were investigated.
```

Keep all the existing results (QFP, discrete vs continuous, hierarchy, secondary observations) with their figures and tables. At the end of the section, add:

```latex
\paragraph{Phase~1 assessment.}
One of five success criteria is met: the top QFP is a robust
$\BISH$ structure visible at coarse discretization. The remaining
four are negative. However, Phase~1 tested only a narrow special
case of the scaffolding hypothesis: one-loop beta functions, small
step size, individual coupling space, smooth running, standard
parameterization. Five substantive alternatives remain untested.
```

### §5 Phase 2: Five Additional Tests (NEW SECTION)

This is entirely new. Structure it as five subsections, one per investigation. Each subsection should have: motivation (2–3 sentences), method (brief), result (quantitative), and verdict (one sentence).

```latex
\section{Phase~2: Systematic Scaffolding Removal}\label{sec:phase2}

Phase~1 tested one specific implementation of the scaffolding
hypothesis. Phase~2 tests five additional implementations, each
removing a different piece of $\LPO$ scaffolding from the SM's
treatment of fermion masses.

\subsection{Two-Loop Beta Functions}\label{sec:two_loop}

\paragraph{Scaffolding removed:} ``One-loop is sufficient.'' If
the mass hierarchy is a perturbative phenomenon visible at the
right loop order, new quasi-fixed-point structure should appear at
two loops that is absent at one loop.

\paragraph{Method.} We implement two-loop gauge coupling beta
functions~\cite{LWX2003} with one-loop Yukawa beta functions
(capturing the dominant next-order effect) and repeat the Phase~1
scan with $1{,}000$ random initial conditions.

\paragraph{Result.} The two-loop correction \emph{destabilizes}
the top QFP rather than creating new structure. The standard
deviation of $y_b/y_t$ at the EW scale decreases by only $3.2\%$
(the success criterion required ${>}50\%$ narrowing). No new
quasi-fixed-points appear for bottom or tau couplings
(\cref{fig:two_loop}).

\paragraph{Verdict:} Higher loop order does not generate new
attractor structure.

\begin{figure}[ht]
  \centering
  \includegraphics[width=0.65\textwidth]{plots_phase2/inv1_two_loop_comparison.png}
  \caption{Distribution of $y_b/y_t$ at the EW scale: one-loop
    (left) versus two-loop gauge + one-loop Yukawa (right). The
    distributions are nearly identical; two-loop corrections do not
    narrow the spread.}
  \label{fig:two_loop}
\end{figure}


\subsection{Large Step-Size Dynamics}\label{sec:large_step}

\paragraph{Scaffolding removed:} ``The discrete map approximates
the continuous flow.'' At large step size, discrete maps can
exhibit bifurcations, periodic orbits, and chaotic behavior absent
in continuous flows. If the Yukawa RG has such structure, it would
be genuinely $\BISH$ with no $\LPO$ analogue.

\paragraph{Method.} We use the one-loop Euler map
$y_{n+1} = y_n + \Delta t \cdot \beta(y_n, g_n)$ with step
counts $N$ ranging from $3$ to $500$, tracking coupling values and
mass ratios at the EW scale as functions of~$N$.

\paragraph{Result.} All couplings and mass ratios converge
monotonically to the continuous-flow values as $N$ increases
(\cref{fig:large_step}). No bifurcation, period-doubling, or
non-monotone structure is observed at any~$N$.

\paragraph{Verdict:} The Yukawa RG discrete map has no dynamics
beyond the continuous flow at any step size.

\begin{figure}[ht]
  \centering
  \includegraphics[width=0.65\textwidth]{plots_phase2/inv2_coupling_vs_N.png}
  \caption{Coupling values at the EW scale versus discrete step
    count~$N$ (Euler map). Monotone convergence to the ODE limit;
    no bifurcation structure.}
  \label{fig:large_step}
\end{figure}


\subsection{Ratio-Space Fixed Points}\label{sec:ratio_space}

\paragraph{Scaffolding removed:} ``Analyze individual couplings.''
The mass hierarchy concerns \emph{ratios}
$r_b = y_b/y_t$, $r_\tau = y_\tau/y_t$, etc. The beta functions
for ratios differ from those for individual couplings---many terms
cancel---and the fixed-point structure can differ.

\paragraph{Method.} We derive the one-loop beta functions for
$r_b$ and $r_\tau$ analytically, scan initial conditions in
$(r_b, r_\tau)$ space with $y_t$ at its QFP value, and plot the
EW-scale ratio plane (\cref{fig:ratio_plane}).

\paragraph{Result.} The coefficient of variation of $r_b(\EW)$
is $1.48$ (wide scatter). Only $13\%$ of initial conditions
produce $r_b$ within $50\%$ of the observed value (the success
criterion required ${>}20\%$ within $50\%$). No attractor is
visible in the $(r_b, r_\tau)$ plane.

\paragraph{Verdict:} Ratio space has no quasi-fixed-point
structure for the $b/t$ or $\tau/t$ mass ratios.

\begin{figure}[ht]
  \centering
  \includegraphics[width=0.65\textwidth]{plots_phase2/inv3_ratio_plane.png}
  \caption{EW-scale values of $(r_b, r_\tau)$ for a grid of
    Planck-scale initial conditions with $y_t$ at its QFP.
    The red star marks observed values. No clustering is visible.}
  \label{fig:ratio_plane}
\end{figure}


\subsection{Threshold-Corrected Piecewise RG}\label{sec:thresholds}

\paragraph{Scaffolding removed:} ``Continuous smooth running.'' In
the physical SM, particles decouple at their mass thresholds; the
beta function changes at each threshold. This is inherently
discrete---a $\BISH$ object---and the self-consistency condition
(masses determine thresholds determine running determine masses)
is a finite algebraic fixed-point problem.

\paragraph{Method.} We implement piecewise one-loop running with
thresholds at $m_t$, $m_b$, $m_\tau$, and $m_c$, modifying gauge
beta function coefficients at each threshold. We iterate the
self-consistency condition from four different initial guesses
(uniform masses at $1$, $10$, $100$~GeV, and random).

\paragraph{Result.} All four initial guesses converge to
$m_t/m_b \approx 1.66$ (observed: $41.3$). The piecewise RG
self-consistency does not recover the mass hierarchy
(\cref{fig:threshold}).

\paragraph{Verdict:} Threshold structure does not determine the
mass hierarchy.

\begin{figure}[ht]
  \centering
  \includegraphics[width=0.65\textwidth]{plots_phase2/inv4_self_consistency.png}
  \caption{Mass ratios versus self-consistency iteration number
    for four initial guesses. All converge to the same wrong
    answer ($m_t/m_b \approx 1.66$ vs.\ observed~$41.3$).}
  \label{fig:threshold}
\end{figure}


\subsection{Koide Phase Dynamics}\label{sec:koide_phase}

\paragraph{Scaffolding removed:} ``Parameterize by individual
Yukawas.'' The Koide formula admits a circulant parameterization
$\sqrt{m_n} = \mu(1 + \sqrt{2}\cos(\delta + 2\pi n/3))$ where
$\delta \approx 2/9$ determines all three charged lepton mass
ratios. If $\delta \to 2/9$ is an infrared attractor of the RG
flow in circulant coordinates, the Koide formula has a dynamical
origin without Sumino's $\LPO$-level all-orders cancellation.

\paragraph{Method.} We implement the coordinate transformation
between $(y_e, y_\mu, y_\tau)$ and $(\mu, \delta)$ via discrete
Fourier transform on $\mathbb{Z}_3$. We evolve the RG in Yukawa
space, project to $(\mu, \delta)$ at each step, and scan initial
$\delta \in [0, 2\pi/3]$ for convergence.

\paragraph{Result.} $0\%$ of initial $\delta$ values produce
$\delta(\EW)$ near $2/9$ (\cref{fig:koide}). The Koide phase has
no infrared attractor in the SM RG.

\paragraph{Verdict:} The Koide phase is UV-sensitive; it has no
dynamical origin in SM infrared dynamics.

\begin{figure}[ht]
  \centering
  \includegraphics[width=0.65\textwidth]{plots_phase2/inv5_koide_phase.png}
  \caption{$\delta(\EW)$ versus $\delta(\text{Planck})$ in the
    Koide circulant parameterization. No convergence to
    $\delta = 2/9$ (dashed line) is observed.}
  \label{fig:koide}
\end{figure}
```

### §6 Discussion (SUBSTANTIALLY REWRITTEN)

Replace the current §4 (Discussion) entirely. The new discussion should have four subsections:

**§6.1 The Scaffolding Principle: Tested and Found Wanting**

This replaces the old §4.1 ("CRM as Diagnostic, Not Generative"). The key change: frame it around the scaffolding principle specifically, not just "generative vs diagnostic." The ten investigations systematically removed five kinds of LPO scaffolding and found nothing underneath. State this clearly.

```latex
\subsection{The Scaffolding Principle Applied to the Mass Hierarchy}
\label{sec:scaffolding_tested}

The scaffolding principle predicted that removing $\LPO$
idealizations from the SM Yukawa sector would expand the solution
space for the mass hierarchy. Ten investigations tested this across
five kinds of scaffolding:

\begin{center}
\small
\begin{tabular}{@{}lll@{}}
\toprule
\textbf{Scaffolding} & \textbf{Investigation} & \textbf{Result} \\
\midrule
One-loop sufficient & Two-loop QFPs (Phase~2, \S\ref{sec:two_loop})
  & No new structure \\
Continuous $\approx$ discrete & Large step-size (Phase~2, \S\ref{sec:large_step})
  & Monotone convergence \\
Individual couplings & Ratio space (Phase~2, \S\ref{sec:ratio_space})
  & No attractor \\
Smooth running & Thresholds (Phase~2, \S\ref{sec:thresholds})
  & Wrong fixed point \\
Standard parameterization & Koide phase (Phase~2, \S\ref{sec:koide_phase})
  & No IR attractor \\
Continuous flow (Phase~1) & Discrete map, $N=10$ to $10{,}000$
  & Same physics \\
\midrule
\multicolumn{2}{@{}l}{Generic initial conditions (Phase~1)}
  & 0/3{,}000 match \\
\multicolumn{2}{@{}l}{Koide from RG (Phase~1)} & $Q = 0.50 \ne 2/3$ \\
\multicolumn{2}{@{}l}{$b/\tau$ attractor (Phase~1)} & Weak (6\%) \\
\multicolumn{2}{@{}l}{Two-loop shift (Phase~1)} & $-0.65\%$ only \\
\bottomrule
\end{tabular}
\end{center}

\noindent
The result is unambiguous: the SM's infrared dynamics do not
determine the fermion mass hierarchy in any parameterization, at
any loop order, at any discretization scale, or under any
threshold structure tested. The mass hierarchy requires genuine
ultraviolet input. The scaffolding principle, applied to this
domain, does not expand the solution space productively---it
expands it into empty space.
```

**§6.2 Scope of the Negative Result**

New subsection. Address whether this refutes the scaffolding principle generally or only for this domain:

```latex
\subsection{Scope of the Negative Result}\label{sec:scope}

The scaffolding principle was tested in one domain---the SM Yukawa
sector---and failed. This domain may be special: the Yukawa
couplings are genuinely free parameters of the SM, with no
dynamical mechanism (infrared or otherwise) constraining them
within the SM itself. Testing whether removing scaffolding reveals
hidden structure in a system that has no hidden structure is not
informative about the principle's general validity.

A fairer test would be a domain where the $\LPO$ result is
\emph{known to be derivable} but the conventional derivation uses
$\LPO$ unnecessarily---for instance, the local conservation law
(Paper~15), which is $\BISH$ and physically sufficient, versus the
global conservation law, which costs $\LPO$. Whether removing
the global-conservation scaffolding reveals a different understanding
of energy conservation is a conceptual question not addressed by
the present numerical investigation.
```

**§6.3 The BISH-Only Domain**

Keep the old §4.2 essentially unchanged, including Table 3 (the six-domain calibration table). This is the paper's positive contribution and doesn't need revision.

**§6.4 CRM Analysis of Mass-Problem Approaches**

Keep the old §4.3 (the compression ratio analysis and Table 2) essentially unchanged. This is original analysis worth preserving.

**§6.5 Limitations**

Expand the old one-paragraph Limitations into a proper subsection:

```latex
\subsection{Limitations}\label{sec:limitations}

\begin{enumerate}
  \item \textbf{One-loop Yukawa dominance.} Phase~2's two-loop
    investigation used two-loop \emph{gauge} with one-loop
    \emph{Yukawa} beta functions, not the full two-loop Yukawa
    system. The full two-loop Yukawa coefficients~\cite{LWX2003}
    include inter-generation mixing via CKM, which could in
    principle create structure absent in the simplified system.

  \item \textbf{Three-loop not tested.} The original hypothesis
    predicted that successive generations might be determined at
    successive loop orders. Three-loop beta functions were not
    implemented.

  \item \textbf{Numerical, not formal.} Unlike Papers~8--17,
    this investigation is a numerical experiment, not a formal
    verification. The statement that the discrete map is $\BISH$
    is trivially true of any finite arithmetic.

  \item \textbf{QFP overshoot.} The one-loop top QFP gives
    $y_t(\EW) \approx 1.29$ versus observed $0.99$---a $30\%$
    overshoot from neglecting threshold corrections, which does
    not affect the qualitative conclusions about attractor structure.

  \item \textbf{Shared encoding pattern.} The ten investigations
    all test variants of the same broad hypothesis (does removing
    $\LPO$ scaffolding reveal mass hierarchy mechanisms?). They
    are not ten independent tests of ten independent hypotheses.
\end{enumerate}
```

### §7 Conclusion (REWRITTEN)

Replace the current conclusion with:

```latex
\section{Conclusion}\label{sec:conclusion}

Ten numerical investigations across two phases test whether the CRM
scaffolding principle---that removing $\LPO$ idealizations from
physics can reveal $\BISH$-level mechanisms invisible in the
conventional formalism---produces new insight into the fermion mass
hierarchy. The answer is no: the Standard Model's infrared dynamics
do not determine the mass spectrum in any parameterization, at any
loop order, or at any discretization scale tested. The thirteen
Yukawa couplings are boundary conditions, not dynamical outputs.
CRM is a powerful diagnostic framework; its generative capacity, at
least for the flavor problem, is null.

The investigation establishes two positive results. First, the top
quasi-fixed-point is a robust $\BISH$ phenomenon, visible at
$N = 10$ discrete steps. Second, the Yukawa RG constitutes the
first domain in the CRM series where the entire computation is
$\BISH$ with no $\LPO$ boundary, confirming that $\LPO$ enters
physics through completed limits of bounded monotone sequences and
nowhere else.

The programme archive is maintained at Zenodo (DOI:
\href{https://doi.org/10.5281/zenodo.18600243}{10.5281/zenodo.18600243}).
```

### Reproducibility Box

Update to include both phases:

```latex
\begin{mdframed}[backgroundcolor=gray!10]
\textbf{Reproducibility Box}
\begin{itemize}
\item \textbf{Repository}:
  \url{https://github.com/AICardiologist/FoundationRelativity}
\item \textbf{Phase~1}: \texttt{paper18/phase1/rg\_mass\_hierarchy.py}
  (${\sim}600$ lines, ${\sim}16$~min)
\item \textbf{Phase~2}: \texttt{paper18/phase2/rg\_phase2.py}
  (${\sim}600$ lines, ${\sim}7$~min)
\item \textbf{Dependencies}: Python~3.9+, NumPy, SciPy, Matplotlib
\item \textbf{Output}: 15~plots (10 Phase~1 + 5 Phase~2), console
  summaries
\item \textbf{Zenodo DOI}:
  \href{https://doi.org/10.5281/zenodo.18600243}{10.5281/zenodo.18600243}
\end{itemize}
\end{mdframed}
```

### AI Methodology Table

Update to reflect the expanded scope:

```latex
\begin{tabular}{@{}lll@{}}
\toprule
\textbf{Task} & \textbf{Human} & \textbf{AI (Claude Opus 4.6)} \\
\midrule
Research direction            & \checkmark & \\
Scaffolding hypothesis        & \checkmark & \checkmark \\
CRM analysis of approaches    & \checkmark & \checkmark \\
Phase~1 beta function code    & & \checkmark \\
Phase~1 numerical scans       & & \checkmark \\
Phase~2 investigation design  & \checkmark & \checkmark \\
Phase~2 implementation        & & \checkmark \\
Result interpretation         & \checkmark & \checkmark \\
Paper writing                 & \checkmark & \checkmark \\
\bottomrule
\end{tabular}
```

### Bibliography Additions

No new references needed beyond what's already cited, unless the coding agent wants to add specific references for threshold corrections. The existing Luo-Wang-Xiao (2003), Pendleton-Ross (1981), Hill (1981), Sumino (2009), Koide (1983), and Randall-Sundrum (1999) citations cover the Phase 2 content.

---

## Figure Management

The paper now references figures from two directories:
- Phase 1 plots: `plots/` (prefix with `phase1/` if the directory was reorganized)
- Phase 2 plots: `plots_phase2/`

The coding agent should adjust `\includegraphics` paths to match the actual file structure. The Phase 1 figures are:

```
plots/plot01_top_qfp.png        → fig:top_qfp
plots/plot10_qfp_basin_N.png    → fig:basin_N
plots/plot04_hierarchy_scatter.png → fig:hierarchy
```

The Phase 2 figures are:

```
plots_phase2/inv1_two_loop_comparison.png → fig:two_loop
plots_phase2/inv2_coupling_vs_N.png      → fig:large_step
plots_phase2/inv3_ratio_plane.png        → fig:ratio_plane
plots_phase2/inv4_self_consistency.png   → fig:threshold
plots_phase2/inv5_koide_phase.png        → fig:koide
```

Total figures: 8 (3 from Phase 1 + 5 from Phase 2). This is manageable for a technical note — each figure earns its place by supporting a specific quantitative claim.

---

## Tone and Framing Notes

The paper should be honest about the negative result without being apologetic. The key rhetorical move: the *thoroughness* of the negative is the contribution. Ten investigations across five kinds of scaffolding, all negative, is more informative than one investigation with an ambiguous result. The paper closes doors systematically.

The scaffolding principle should be presented as a genuine intellectual contribution — it's the first attempt to use CRM generatively, and the idea (that LPO idealizations constrain solution spaces) is sound even if the specific application failed. The failure is domain-specific, not principle-general.

Avoid:
- Apologizing for negative results
- Claiming the scaffolding principle is "refuted" in general (it's tested in one domain)
- Inflating the BISH-only domain finding to compensate for the negative
- Defensive language about the investigation being "just numerical"

Do:
- State the negative clearly and quantitatively
- Frame the ten-investigation sweep as methodologically rigorous
- Present the scaffolding principle as worth testing even though it failed here
- Let the BISH-only domain finding stand on its own merits
- Acknowledge honestly that the paper's mathematical content is modest

---

## Page Budget

The current Phase 1 paper is approximately 8 pages. The combined paper should be 12–14 pages:
- §1 Introduction: 1 page (slightly expanded)
- §2 Scaffolding Hypothesis: 1.5 pages (new)
- §3 Yukawa System: 1 page (condensed from old §2)
- §4 Phase 1 Results: 2.5 pages (unchanged)
- §5 Phase 2 Results: 3 pages (new, ~0.6 page per investigation)
- §6 Discussion: 2 pages (rewritten)
- §7 Conclusion: 0.5 page
- Back matter: 1.5 pages

This is appropriate for a technical note with substantive content.
