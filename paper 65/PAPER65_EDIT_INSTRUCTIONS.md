# PAPER 65 EDIT INSTRUCTIONS
## For Writing/Lean Agent
### Priority: HIGH — fixes a referee-exploitable error and upgrades the non-cyclic contribution

---

## EDIT 1: THE DIAGONALITY PRECISION FIX (CRITICAL)

### Problem

The paper repeatedly says "the Gram matrix diagonalises" or "G is diagonal (b = 0)" for the free/cyclic case. This is imprecise and a referee will object.

The ℤ-Gram matrix for the basis {w₀, ω·w₀} is:

```
G_ℤ = [ 2h·Nm(1)        h·(ω̄ + ω)     ]  =  [ 2h        h·Tr(ω) ]
      [ h·(ω̄ + ω)       2h·Nm(ω)       ]     [ h·Tr(ω)  2h·Nm(ω) ]
```

The off-diagonal is h·Tr(ω), which is NONZERO whenever Tr(ω) ≠ 0 (e.g., d ≡ 1, 2 mod 4).

What IS "diagonal" (or rather, scalar) is the **𝒪_K-Hermitian form**: since W_int is rank 1 over 𝒪_K, the Hermitian pairing is determined by a single value h = H(w₀, w₀). The ℤ-Gram determinant then equals h² · |Δ_K| by the trace form computation, regardless of whether the ℤ-matrix has zero off-diagonal entries.

### Fix locations (5 sites)

---

#### Site 1: Introduction, lines 108–115

**FIND:**
```latex
The mechanism is as follows.  The Gram matrix $G$ of the rank-2 Weil
lattice $W_{\mathrm{int}}$ satisfies $\det(G) = \disc(F) \cdot
|\Delta_K|$ (Schoen \cite{Schoen98}, Milne \cite{Milne99}).
When $h_K = 1$, the ring $\cO_K$ is a PID, so $W_{\mathrm{int}}$
is free and $G$~is diagonal.  For cyclic cubics, the
conductor--discriminant formula gives $\disc(F) = f^2$.  Together
with the Hodge--Riemann positivity constraint, this forces
$h = f$.
```

**REPLACE WITH:**
```latex
The mechanism is as follows.  The Gram matrix $G$ of the rank-2 Weil
lattice $W_{\mathrm{int}}$ satisfies $\det(G) = \disc(F) \cdot
|\Delta_K|$ (Schoen \cite{Schoen98}, Milne \cite{Milne99}).
The lattice carries a rank-1 $\cO_K$-Hermitian structure: the
$\cO_K$-module $W_{\mathrm{int}}$ has rank~1, so the Hermitian
self-pairing is determined by a single positive rational number
$h = H(w_0, w_0)$.  The $\Z$-Gram determinant satisfies
$\det(G) = h^2 \cdot |\Delta_K|$ via the trace form
$B(x,y) = \mathrm{Tr}_{K/\Q}\, H(x,y)$.
For cyclic cubics, the conductor--discriminant formula gives
$\disc(F) = f^2$.  Combining: $h^2 \cdot |\Delta_K| = f^2 \cdot
|\Delta_K|$, so $h = f$ by positivity.
```

---

#### Site 2: Preliminaries §2.3, lines 226–234

**FIND:**
```latex
Its Gram matrix $G = \bigl[\begin{smallmatrix} a & b \\
b & c \end{smallmatrix}\bigr]$ satisfies
\begin{equation}\label{eq:det}
  \det(G) = ac - b^2 = \disc(F) \cdot |\Delta_K|.
\end{equation}
By Steinitz's theorem, $W_{\mathrm{int}} \cong \cO_K \oplus \fA$
for a unique ideal class $[\fA] \in \mathrm{Cl}(\cO_K)$.
The self-intersection degree is $h = G_{11}$ (the $(1,1)$-entry
of a reduced Gram matrix).
```

**REPLACE WITH:**
```latex
Its $\Z$-Gram matrix $G$ on any $\Z$-basis satisfies
\begin{equation}\label{eq:det}
  \det(G) = \disc(F) \cdot |\Delta_K|
\end{equation}
(Schoen \cite{Schoen98}, Milne \cite{Milne99}).
By Steinitz's theorem, $W_{\mathrm{int}} \cong \fA$ as
$\cO_K$-modules for a unique ideal class
$[\fA] \in \mathrm{Cl}(\cO_K)$.  As a rank-1 $\cO_K$-module,
the Hermitian self-pairing is determined by a single value
$h = H(w_0, w_0) \in \Q^{>0}$.  For a $\Z$-basis
$\{\alpha, \beta\}$ of~$\fA$, the $\Z$-Gram matrix is
\[
  G = h \cdot \begin{pmatrix}
    2\,\Nm(\alpha) & \alpha\bar\beta + \bar\alpha\beta \\
    \alpha\bar\beta + \bar\alpha\beta & 2\,\Nm(\beta)
  \end{pmatrix},
\]
with $\det(G) = h^2 \cdot \Nm(\fA)^2 \cdot |\Delta_K|$.
```

**NOTE:** This also fixes a mathematical issue — the Steinitz decomposition is $W_{\mathrm{int}} \cong \fA$ (rank-1 projective), not $\cO_K \oplus \fA$ (rank-2 free). The latter is the Steinitz normal form for rank-2 modules. Since W_int has 𝒪_K-rank 1, it's isomorphic to a single ideal $\fA$.

---

#### Site 3: Preliminaries §2.4, lines 236–250

**FIND:**
```latex
For $h_K = 1$, the module $W_{\mathrm{int}}$ is free, $G$~is
diagonal ($b = 0$), and $h^2 \cdot |\Delta_K| = f^2 \cdot
|\Delta_K|$, giving $h = f$.
```

**REPLACE WITH:**
```latex
For $h_K = 1$, the ideal $\fA$ is principal ($\fA = \cO_K$,
$\Nm(\fA) = 1$), so $\det(G) = h^2 \cdot |\Delta_K| = f^2 \cdot
|\Delta_K|$, giving $h = f$.  (The $\Z$-Gram matrix is not
literally diagonal unless $\mathrm{Tr}(\omega) = 0$; what is
``scalar'' is the $\cO_K$-Hermitian form, being rank~1.)
```

---

#### Site 4: Proof of Theorem 3.1, lines 285–302

**FIND:**
```latex
\begin{proof}
The determinant identity~\eqref{eq:det} gives
$\det(G) = f^2 \cdot |\Delta_K|$.
When the lattice is free ($\fA$ principal, $\Nm(\fA) = 1$),
the Gram matrix diagonalises as $G =
\bigl[\begin{smallmatrix} h & 0 \\ 0 & c \end{smallmatrix}\bigr]$
with $hc = f^2 \cdot |\Delta_K|$.
The $\cO_K$-scaling constraint forces $c = h \cdot |\Delta_K|$,
giving $h^2 = f^2$ and hence $h = f$ by positivity.

When $\fA$ is non-principal with $\Nm(\fA) = N$, the
module $W_{\mathrm{int}} \cong \cO_K \oplus \fA$ has
Gram matrix with $\det(G) = f^2 \cdot |\Delta_K|$ and
the off-diagonal entry constrained by the ideal structure.
The first diagonal entry satisfies $h = f / N$, which is
positive since $N \mid f$ in the cyclic cubic setting (the
conductor $f$ factors through the class group of~$K$).
\end{proof}
```

**REPLACE WITH:**
```latex
\begin{proof}
The determinant identity~\eqref{eq:det} gives
$\det(G) = f^2 \cdot |\Delta_K|$.  The Weil lattice has
$\cO_K$-rank~1, with Hermitian self-pairing $h = H(w_0, w_0)$
and Steinitz class~$[\fA]$.  From the explicit Gram matrix
(see~\S\ref{sec:prelim}):
\[
  \det(G) = h^2 \cdot \Nm(\fA)^2 \cdot |\Delta_K|.
\]
Equating with the determinant identity and cancelling
$|\Delta_K| > 0$:
\[
  h^2 \cdot \Nm(\fA)^2 = f^2.
\]
Since $h > 0$ (Hodge--Riemann) and $\Nm(\fA) > 0$, we obtain
$h \cdot \Nm(\fA) = f$.
\end{proof}
```

**NOTE:** This proof is now clean and complete. The old proof had two unjustified steps ("𝒪_K-scaling constraint forces c = h·|Δ_K|" and "N | f"). The new proof goes directly from det(G) = h²·Nm(𝔄)²·|Δ_K| = f²·|Δ_K| to h·Nm(𝔄) = f.

---

#### Site 5: Discussion §7.1, lines 572–579

**FIND:**
```latex
The $\Z/3\Z$~Galois symmetry of cyclic cubics is the structural
reason for the identity $h = f$.  This symmetry forces the Gram
matrix to diagonalise (when the lattice is free), collapsing the
two-parameter family $\{(a, b, c) : ac - b^2 = \disc(F) \cdot
|\Delta_K|\}$ to a one-parameter family $\{(h, 0, c)\}$.
For $S_3$~cubics, this symmetry is absent: the Gram matrix has a
free off-diagonal entry, and the self-intersection degree $h$ is
no longer determined by the conductor alone.
```

**REPLACE WITH:**
```latex
The $\Z/3\Z$~Galois symmetry of cyclic cubics is the structural
reason for the identity $h = f$.  For cyclic cubics, the Weil
lattice is a rank-1 $\cO_K$-module (the Galois action makes
$W_{\mathrm{int}}$ isotypic), so the $\cO_K$-Hermitian form is
determined by a single scalar $h = H(w_0, w_0)$.  The identity
$h \cdot \Nm(\fA) = f$ then follows from the determinant equation.

For $S_3$~cubics, this rank-1 structure may fail: the Weil lattice
need not be isotypic under~$\cO_K$, and the $\Z$-Gram matrix
$G = \bigl[\begin{smallmatrix} a & b \\ b & c
\end{smallmatrix}\bigr]$ has $a \ne c$ in general.  The
self-intersection depends on the choice of generator, and the
natural invariant is the $\mathrm{GL}_2(\Z)$-equivalence class
of~$G$---a class of binary quadratic forms, not a single integer.
The cyclic identity $h \cdot \Nm(\fA) = f$ is the degenerate
case where this form class collapses to a scalar.
```

---

## EDIT 2: FORM-CLASS REFRAMING FOR NON-CYCLIC SECTION

### Problem

The non-cyclic section (§4.6, Table 2) reports "#Gram" = total number of reduced BQF forms of determinant disc(F)·|Δ_K|. But most of these forms are NOT compatible with the 𝒪_K-Hermitian structure. The paper presents this as "multiple candidate h values" without explaining why there are multiple candidates or what would resolve the ambiguity.

### Fix

Add a new remark after Proposition 3.3 (the non-cyclic failure proposition, around line 355):

**INSERT AFTER line 355:**
```latex
\begin{remark}[The form-class invariant]\label{rem:formclass}
For non-cyclic cubics, the self-intersection degree~$h$ is not
a well-defined scalar invariant: the $\Z$-Gram matrix
$G = \bigl[\begin{smallmatrix} a & b \\ b & c
\end{smallmatrix}\bigr]$ has $a \ne c$ in general, and $h$
depends on the choice of lattice basis.  The basis-independent
invariant is the $\mathrm{GL}_2(\Z)$-equivalence class of the
positive-definite binary quadratic form~$[a, b, c]$ with
$ac - b^2 = \disc(F) \cdot |\Delta_K|$.

For cyclic cubics, this class is the ``scalar'' class
$(h, 0, h|\Delta_K|)$, which collapses to a single integer~$h$.
The identity $h \cdot \Nm(\fA) = f$ is the statement that this
scalar class is determined by the conductor.  For $S_3$~cubics,
the form class is generically non-scalar, and the natural
question becomes: \emph{which form class occurs, and what
arithmetic invariant of~$(K, F)$ determines it?}

This reformulation connects the exotic Weil class to the
classical theory of binary quadratic forms and ideal class
groups.  We leave the identification of the arithmetic predictor
as an open problem for future work.
\end{remark}
```

### Also fix Table 2 caption (line 460):

**FIND:**
```latex
\caption{Sample non-cyclic cubics: Gram matrix multiplicity.}
```

**REPLACE WITH:**
```latex
\caption{Sample non-cyclic cubics: number of reduced positive-definite
binary quadratic forms of determinant $\disc(F) \cdot |\Delta_K|$.
Not all forms are compatible with the $\cO_K$-Hermitian structure;
identifying the correct form class is an open problem.}
```

---

## EDIT 3: REDUCE UNDETERMINED PAIRS (COMPUTATION)

### Problem

480/1220 = 39% undetermined is optically bad. The h_K = 2 cases (70 undetermined) should be fully resolvable since the class group has only 2 elements.

### Fix

Update the Python computation (`p65_compute.py`) to exhaustively check all ideal classes for h_K ≤ 4. For each class [𝔄] ∈ Cl(K):
1. Compute Nm(𝔄)
2. Check if f/Nm(𝔄) is representable as a norm from K (i.e., ∃ x,y ∈ ℚ with f/Nm(𝔄) = x² + dy²)
3. If yes, that's the Steinitz class; record h = f/Nm(𝔄)

This should resolve at minimum the 70 pairs at h_K = 2, and likely most of the 27 at h_K = 3 and 124 at h_K = 4. Target: < 200 undetermined (down from 480).

Update Table 1 accordingly after rerunning.

---

## EDIT 4: STEINITZ MODULE RANK (MINOR BUT IMPORTANT)

### Problem

Line 231 says $W_{\mathrm{int}} \cong \cO_K \oplus \fA$. This is the Steinitz form for a **rank-2** module. But the Weil lattice has 𝒪_K-rank 1 (it's the image of a single exotic Weil class under the 𝒪_K-action). The correct statement is $W_{\mathrm{int}} \cong \fA$ as 𝒪_K-modules.

The rank-2 statement appears because the ℤ-rank is 2 and the paper conflates ℤ-rank with 𝒪_K-rank. This needs to be consistent throughout.

### Locations to fix

- Line 121: "$W_{\mathrm{int}} \cong \cO_K \oplus \fA$" → "$W_{\mathrm{int}} \cong \fA$ as $\cO_K$-modules"
- Line 231: same fix (already covered in Edit 1, Site 2)
- Line 296: "$W_{\mathrm{int}} \cong \cO_K \oplus \fA$" → remove (already covered in Edit 1, Site 4)

---

## SUMMARY OF CHANGES

| Edit | Priority | Type | Effect |
|------|----------|------|--------|
| 1 (diagonality) | CRITICAL | Precision | Blocks referee objection |
| 2 (form-class) | HIGH | Conceptual | Upgrades non-cyclic from negative result to open question |
| 3 (undetermined) | MEDIUM | Computation | Reduces undetermined from 39% to ~15% |
| 4 (module rank) | MEDIUM | Correctness | Fixes 𝒪_K-rank 1 vs ℤ-rank 2 confusion |

After these edits, the paper should be reviewed for any remaining instances of "diagonal" applied to the ℤ-Gram matrix. Search for: `diagonal`, `diag`, `b = 0`, `off-diagonal.*vanish`.
