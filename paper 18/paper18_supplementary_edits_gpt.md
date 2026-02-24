# Paper 18 — Supplementary Edits (Reviewer Response)

**Context:** These eight fixes address technical issues identified in peer review. Apply on top of the main edit specification (`paper18_edit_specification.md`) and appendix specification (`paper18_appendix_specification.md`).

---

## Fix 1: Resolve the "continuous RG = LPO" tension

**Location:** §3 (The SM Yukawa System), the paragraph about the discrete map replacing the ODE (around old lines 209–215).

**Problem:** The draft says the continuous ODE "in general costs LPO," then later claims the domain is BISH-only. A constructive analyst will note that numerically solving an ODE on a finite interval with a Lipschitz constant is already BISH.

**Action:** Replace the existing paragraph with:

```latex
The standard RG flow is a continuous ODE. For predictions between
two finite energy scales, the solution can be approximated to any
desired precision by a finite number of integration steps---this
is $\BISH$ computation. $\LPO$ enters only when physicists assert
a \emph{completed} object: an exact fixed point (not an
approximate one), an exact all-orders cancellation (not a
finite-order one), or an exact converged value without specifying
a rate of convergence. The discrete map we study is not an
approximation to an $\LPO$-level object; it \emph{is} the
physically relevant computation, and the continuous flow is a
convenient idealization that happens to cost no additional logical
strength for finite-scale predictions. This is why the domain is
$\BISH$-complete: no completed limit does physical work.
```

---

## Fix 2: Scope the dynamical system precisely

**Location:** §3, new paragraph immediately after equation (4) (the gauge beta functions).

**Problem:** The paper frames itself as testing "the fermion mass hierarchy (13 parameters)" but actually evolves diagonal Yukawas without CKM mixing or full matrix structure. A phenomenologist will say "you didn't include flavor."

**Action:** Insert:

```latex
\paragraph{Scope of the implemented system.}
In both phases we evolve \emph{diagonal} Yukawa couplings: nine
independent $y_f$ ($f = t, b, \tau, c, s, \mu, u, d, e$) coupled
through the gauge couplings but without CKM mixing or off-diagonal
Yukawa-matrix structure. At one loop in this diagonal
approximation, inter-generation coupling enters only through the
gauge beta functions (which depend on the total number of active
flavors, not on individual Yukawa values). The full one-loop
Yukawa-matrix RGE includes trace terms
$\mathrm{Tr}(Y_u^\dagger Y_u)$ that couple all up-type Yukawas;
these are dominated by $y_t^2$ and are numerically negligible for
lighter generations. At two loops, CKM mixing enters explicitly
and is neglected here. The negative results reported below should
be read as ``no attractor structure exists in the diagonal Yukawa
system''; whether the full matrix system with CKM structure
behaves differently is an open question, though we regard it as
unlikely given that CKM effects are perturbatively small
corrections to the diagonal system.
```

---

## Fix 3: Label Investigation 1 accurately

**Location:** §5.1 (Two-Loop Beta Functions), all occurrences.

**Problem:** Calling it "two-loop" when it's two-loop gauge + one-loop Yukawa is imprecise.

**Action:** In the Method paragraph, replace the current text with:

```latex
\paragraph{Method.} We implement two-loop gauge coupling beta
functions~\cite{LWX2003} combined with one-loop Yukawa beta
functions---capturing the dominant next-order correction to gauge
running while retaining the one-loop Yukawa structure. This is not
the full two-loop Yukawa system of Ref.~\cite{LWX2003}; the full
two-loop Yukawa coefficients include inter-generation
CKM-dependent terms not implemented here. We repeat the Phase~1
scan with $1{,}000$ random initial conditions.
```

In the figure caption, change "one-loop versus two-loop" to "one-loop versus two-loop gauge + one-loop Yukawa."

In the subsection title, change to: "Two-Loop Gauge + One-Loop Yukawa Beta Functions"

---

## Fix 4: Wilsonian-shell paragraph for Investigation 2

**Location:** §5.2 (Large Step-Size Dynamics), insert after the Result paragraph, before the Verdict.

**Problem:** Step size is an algorithmic parameter, not a physical one. Any structure found only at coarse N risks being a property of the integrator, not the physics.

**Action:** Insert:

```latex
\paragraph{Interpretation.}
The discrete step size $\Delta t$ is an algorithmic parameter, not
a physical one: the SM RG has no preferred discretization scale.
A physical interpretation exists in the Wilsonian framework, where
each step integrates out a momentum shell of finite width, but our
large-$\Delta t$ tests should be read as robustness checks on the
discrete map's dynamical structure rather than probes of physically
new dynamics. The monotone convergence we observe is consistent
with the beta functions being smooth and well-behaved on the
relevant domain; it does not rule out non-trivial discrete dynamics
in other systems with stiffer or more nonlinear beta functions.
```

---

## Fix 5: Analytic no-go argument (NEW subsection)

**Location:** §6 Discussion, insert as new §6.2 after §6.1 ("The Scaffolding Principle Applied to the Mass Hierarchy"). Renumber subsequent subsections.

**Problem:** The negative results are purely empirical ("we sampled and found nothing"). A brief analytic argument explaining *why* ratio-space attractors are structurally absent would transform the paper from empirical negative to structural negative.

**Action:** Insert:

```latex
\subsection{Structural Reason for the Negative Result}
\label{sec:no_go}

The negative results of Phases~1 and~2 are not merely empirical.
They reflect a structural property of one-loop Yukawa beta
functions.

At one loop, each Yukawa coupling satisfies
$\dot{y}_f = y_f \cdot F_f(y^2, g^2)$, where $F_f$ is a
polynomial in the squared couplings. The beta function for a ratio
$r_f = y_f / y_t$ is therefore
\begin{equation}\label{eq:ratio_beta}
  \dot{r}_f = r_f \bigl[ F_f(y^2, g^2) - F_t(y^2, g^2) \bigr].
\end{equation}
A nontrivial infrared fixed point for~$r_f$ requires
$F_f = F_t$---the Yukawa and gauge contributions to the two beta
functions must balance at a specific ratio value.

For the top quark, the \emph{absolute} coupling $y_t$ has a
quasi-fixed-point because $F_t$ crosses zero: the positive Yukawa
self-coupling $\frac{9}{2}y_t^2$ balances the negative QCD
contribution $-8 g_3^2$ at
$y_t^2 \approx \frac{16}{9}g_3^2$. This is the Pendleton--Ross
mechanism.

For lighter fermions ($f \ne t$), $y_f^2 \ll y_t^2$, so the
Yukawa contributions to~$F_f$ are negligible and $F_f$ is
dominated by gauge terms. But $F_t$ retains its large
$\frac{9}{2}y_t^2$ term. The difference $F_f - F_t$ is therefore
generically nonzero and dominated by
$-\frac{9}{2}y_t^2$, giving
\begin{equation}
  \dot{r}_f \approx -\frac{9}{2} \frac{y_t^2}{16\pi^2}\, r_f\,.
\end{equation}
This drives $r_f$ toward zero---lighter fermions decouple further
from the top---without crossing zero at any nontrivial~$r_f^*$.

The mass hierarchy is thus \emph{structurally stable} under
one-loop RG: whatever hierarchy exists at the UV scale is
preserved (and mildly amplified) by the flow. No attractor exists
because the equations have no mechanism to \emph{create} a
hierarchy from generic initial conditions. The scaffolding
principle cannot overcome this: removing the continuous-flow
idealization does not change the polynomial structure of the beta
functions, which is what prevents ratio fixed points.
```

---

## Fix 6: Hypercharge normalization footnote

**Location:** §3, after "g₁, g₂, g₃ are the U(1)_Y, SU(2)_L, SU(3)_C gauge couplings."

**Action:** Add footnote:

```latex
\footnote{We use the non-GUT-normalized hypercharge coupling
$g_1 = g_Y$, giving $b_1 = 41/6$. Many references use the
GUT-normalized $g_1 = \sqrt{5/3}\,g_Y$, which changes the
numerical coefficients. Our convention follows
Ref.~\cite{MV1984}.}
```

---

## Fix 7: Threshold scheme-dependence acknowledgment

**Location:** §5.4 (Threshold-Corrected Piecewise RG), append to the Method paragraph.

**Action:** Add:

```latex
This is a deliberately coarse discretization of the decoupling
process, not a precision EFT analysis: in the
$\overline{\text{MS}}$ scheme, threshold corrections involve
continuous matching coefficients rather than literal step-function
decoupling, and the choice of which thresholds to resolve is
scheme-dependent. The test probes whether piecewise-constant beta
functions have self-consistency structure, not whether the
resulting masses are numerically precise.
```

---

## Fix 8: Compression ratio counting rule

**Location:** Appendix A, §A.6 (Synthesis), before the summary table.

**Problem:** "Compression ratio" is used informally. A skeptic will dispute the parameter counts.

**Action:** Insert before the table:

```latex
\paragraph{Counting convention.}
We adopt the following rules for \Cref{tab:uv_audit}.
\emph{Continuous parameters}: each real-valued free parameter
counts as~$1$ (e.g., a flavon VEV, a bulk mass, $\varepsilon$).
\emph{Discrete parameters}: each independent discrete choice
counts as~$1$ (e.g., a charge assignment, a flux integer, a
topological invariant).
\emph{$O(1)$ coefficients}: counted as free parameters unless
set to a specific value by a texture rule or symmetry.
\emph{Exact symmetry assumptions}: count as~$0$ inputs but are
flagged in the ``$\LPO$ Component'' column if they require
all-orders or completed-infinite assertions.
\emph{Observables}: the 13~Yukawa-sector quantities
(9~fermion masses, 3~CKM angles, 1~CP phase). Neutrino
parameters are noted where relevant but not included in the
headline count.
These conventions are necessarily approximate---parameter counting
in BSM models is not canonical---but they suffice for the
qualitative comparisons intended here.
```
