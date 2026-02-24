# Paper 17 — Edit Specification (Reviewer Response)

**Input:** `paper17_writeup.tex` (current draft, 1,221 lines)  
**Output:** `paper17_writeup_v2.tex`  
**Scope:** Six targeted fixes. No structural reorganization. The paper's architecture (Part A / Part B / Part C) is sound; these edits tighten claims to match proofs and address physics framing issues.

---

## Fix 1: Rewrite Part B headline to match the proved equivalence

**Problem:** The Introduction and Part B theorem statement say "the assertion that the entropy density S(A)/A converges as A → ∞ is equivalent to LPO." But the formal equivalence actually proved is about the *encoded* two-point sequence S_α(n), driven by a running maximum between two fixed areas A_lo and A_hi — not the general large-area limit.

**Location:** Three places need adjustment:

**(a) The Introduction** — wherever Part B is summarized (around line 109 area and the "three answers" bullet list), change the description from the general convergence claim to:

```latex
(B)~the assertion that a natural bounded monotone surrogate
sequence---constructed from entropy densities at two areas via
a running-maximum encoding---converges for all binary sequences
$\alpha$ is equivalent to $\LPO$;
```

**(b) Theorem statement** (around line 509–514) — rewrite to:

```latex
\begin{theorem}[Part B: encoded entropy convergence
  $\Leftrightarrow$ LPO]\label{thm:equiv}
Over $\BISH$, the assertion that the encoded entropy density
sequence $S_\alpha(n)$ converges for all binary sequences
$\alpha$ is equivalent to the Limited Principle of Omniscience.
\end{theorem}
```

**(c) Add a bridge lemma** — immediately after the theorem (or in a remark following it), add:

```latex
\begin{remark}\label{rem:bridge}
Since the encoded sequence $S_\alpha(n)$ takes values in
$\{S(A_{\mathrm{lo}})/A_{\mathrm{lo}},\;
S(A_{\mathrm{hi}})/A_{\mathrm{hi}}\}$, any convergent
subsequence of the general density sequence
$S(A)/A$ as $A \to \infty$ that passes through both values
must, in particular, make $S_\alpha(n)$ converge.
Consequently, convergence of the general density limit
$S(A)/A \to L$ implies convergence of $S_\alpha(n)$ for
all~$\alpha$, so the general limit also costs $\LPO$.
The encoding does not weaken the calibration; it makes
the $\LPO$ content visible in a controlled two-point setting.
\end{remark}
```

---

## Fix 2: Move the shared encoding template caveat into Part B

**Problem:** The "shared encoding template" observation is currently buried in Limitations. The reviewer correctly notes it should appear in Part B itself so it reads as deliberate calibration rather than an afterthought.

**Location:** §5 (Part B), after the equivalence theorem and bridge remark, add a paragraph:

```latex
\paragraph{Shared encoding infrastructure.}
The backward direction uses the same running-maximum encoding
as Papers~8, 13, 14, and~15: a binary sequence $\alpha$ drives
a two-valued bounded monotone sequence whose convergence encodes
$\LPO$. The domain-specific content is the \emph{gap lemma}
(\Cref{lem:gap})---the existence of two areas with distinct
entropy densities. The encoding infrastructure is inherited from
earlier papers. We regard this as a structural feature of the
programme, not a weakness: the pattern $\BMC \leftrightarrow
\LPO$ is uniform across domains precisely because the encoding
template is uniform, while the physical content that feeds it
differs in each domain.
```

If this material already appears verbatim in Limitations, remove or shorten it there to avoid redundancy, replacing it with a forward reference: "The shared encoding template is discussed in §5.2."

---

## Fix 3: Counting scheme convention sentence

**Problem:** The generating function Z(t) with degeneracy factor (2k+2) doesn't match the standard (2j+1) = (k+1) without explanation. The reviewer (and our earlier review) both flag this. Experts will ask "which counting scheme is this?"

**Location:** §3.3 (or wherever Z(t) is introduced, around lines 531–541). Add immediately after the definition of Z(t):

```latex
\paragraph{Counting convention.}
We use the simplified puncture-counting model without the
projection constraint ($\omega = 0$ specialization), following
the treatment of Meissner~\cite{Meissner2004}. The degeneracy
factor $(2k+2)$ per puncture accounts for both the magnetic
quantum number ($2j+1 = k+1$ states) and the two orientations
of the puncture (inward/outward), giving $2(k+1) = 2k+2$. This
matches the $\omega = 0$ generating function of the standard
treatment. The value of~$t^*$ (and hence the Barbero--Immirzi
parameter~$\gamma$) depends on this convention; the full
projection-constrained counting gives a slightly different
$t^*$, as noted in Limitation~1.
```

This simultaneously resolves the degeneracy factor question and pins down the counting scheme for experts.

---

## Fix 4: Soften the log correction "LQG-distinguishing" claim

**Problem:** The paper says the −3/2 log correction "distinguishes LQG from other approaches." This is too strong: the same −3/2 appears in CFT-based arguments (Carlip), and within LQG the coefficient historically differed between U(1) and SU(2) treatments.

**Location:** Wherever this claim appears (likely in §6 or §7, the Discussion / Strominger-Vafa section). Replace language like "distinguishes LQG from other approaches" with:

```latex
The $-3/2$ logarithmic correction is a meaningful discriminator
between counting prescriptions and a consistency check across
frameworks, but it is not a unique LQG fingerprint: the same
coefficient appears in Carlip-type conformal field theory
arguments and in other symmetry-based
treatments~\cite{Carlip2000}. Within LQG, the coefficient
historically differed between the $\mathrm{U}(1)$
isolated-horizon treatment ($-1/2$) and the $\mathrm{SU}(2)$-invariant
treatment ($-3/2$); the latter is now standard. The CRM
calibration applies to the specific counting model implemented
here (\S\ref{sec:Z}), not to the log correction as a universal
LQG prediction.
```

**New bibliography entry:**

```latex
\bibitem[Carlip(2000)]{Carlip2000}
S.~Carlip.
\newblock Logarithmic corrections to black hole entropy from the
  Cardy formula.
\newblock \emph{Classical and Quantum Gravity}, 17:4175--4186, 2000.
```

---

## Fix 5: Demote Theorem 7 (the −3/2 identity) to a remark

**Problem:** Theorem 7 states "For A > 1, −(1/2)log(A³) = −(3/2)log A." As the reviewer notes, this reads as a parody theorem to anyone outside the Lean-audit culture. The mathematical content is a `ring` lemma. The Lean snippet is valuable (it shows the axiom profile is clean); the theorem environment is not.

**Location:** §5.5 or wherever Theorem 7 / `thm:coeff` appears (around lines 583–600).

**Action:** Replace `\begin{theorem}` / `\end{theorem}` with a remark:

```latex
\begin{remark}[Algebraic extraction of the $-3/2$ coefficient]
\label{rem:coeff}
Given the $A^3$ scaling of the Hessian determinant (axiomatized
in \texttt{saddle\_point\_expansion}), the coefficient extraction
is purely algebraic:
$-\frac{1}{2}\log(A^3) = -\frac{3}{2}\log A$. In Lean this is
a two-line proof using \texttt{Real.log\_pow} and \texttt{ring},
carrying no physics axioms. The physical content---that the
Hessian determinant scales as $\kappa A^3$---resides entirely
in the axiomatized Laplace method, not in this algebraic step.
\end{remark}
```

Keep the Lean `lstlisting` immediately after. This preserves the axiom-audit value while not overstating what's proved.

---

## Fix 6: Add constructive witness for Z(0⁺) = ∞

**Problem:** The divergence of Z(t) as t → 0⁺ is axiomatized, but a simple constructive witness exists and would strengthen the paper.

**Location:** §5.4 (The Generating Function Z(t)), wherever the limiting behavior at 0⁺ is discussed (around lines 534–541).

**Action:** Add after the axiomatization statement:

```latex
\paragraph{Constructive witness for $Z(0^+) = \infty$.}
For any $M > 0$, the partial sum of the first $N$ terms of $Z(t)$
satisfies $\sum_{k=1}^{N} (2k+2)\,e^{-t\,a(k)} \ge N \cdot 2
\cdot e^{-t\,a(N)}$ (since each term exceeds the last). For fixed
$N$, this exceeds $M$ whenever $t < \log(2N/M) / a(N)$. Thus for
any $M$ we can constructively produce a $t_M > 0$ with
$Z(t_M) > M$: take $N = \lceil M \rceil$ and
$t_M = \log(2N/M)/(2N)$ (using $a(k) \le 2k$ for a crude bound).
This is a finite computation---$\BISH$ without axiomatization.
```

Alternatively, if the paper already axiomatizes this and changing it would require Lean modifications, keep the axiom but add a sentence: "A constructive witness exists (pick t small enough that the first N terms exceed M); we axiomatize for uniformity with the other generating-function properties."

---

## Summary of Changes

| Fix | Section | Nature | Priority |
|---|---|---|---|
| 1 | Part B headline + bridge lemma | Claim-proof alignment | High |
| 2 | Part B, shared encoding caveat | Framing (move from Limitations) | High |
| 3 | §3.3, counting convention | Physics precision | High |
| 4 | §7, log correction claim | Physics framing | Medium |
| 5 | §5.5, Theorem 7 → Remark | Presentation | Medium |
| 6 | §5.4, Z(0⁺) witness | Strengthening | Low |

None of these changes affect the Lean formalization. All are LaTeX-only edits. Total added text: approximately 1.5 pages. No sections removed or restructured.
