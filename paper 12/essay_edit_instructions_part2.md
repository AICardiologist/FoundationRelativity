# Additional Edit Instructions for essay_constructive_history.tex (Paper 12)
# ================================================================
# Part 2: The Cognitive Value of Idealization
#
# These edits ADD to the previous edit instructions (essay_edit_instructions.md).
# Apply the previous edits (Edits 1-5) first, then these (Edits 6-8).
#
# These edits address the question: if BISH is enough, why did every
# great physicist use the cathedral? The answer: idealization has zero
# computational content but enormous cognitive value. The calibration
# table becomes a cost-benefit analysis of idealization.
# ================================================================


## EDIT 6: Expand Section 7 — "What Could Have Been Done Instead"
## Location: AFTER the keymessage block that ends with
##   "The constructive alternative is not a hypothetical programme---it is what physicists already do."
## This is around line 1099-1100.
## Anchor string (unique): "The constructive alternative is not a hypothetical programme---it is what physicists already do."
## Action: INSERT a new subsection AFTER the \end{keymessage} that follows this line.
## (That \end{keymessage} is at line 1100.)

INSERT AFTER the line "\end{keymessage}" that follows "The constructive alternative is not a hypothetical programme---it is what physicists already do.":

```latex

\subsection*{The cognitive value of idealization}

If the constructive alternative suffices for every prediction, a natural objection arises: why did every great physicist of the twentieth century use the cathedral?
Einstein was not confused.
Von~Neumann was not following convention.
Dirac was not ignorant of alternatives.
They chose the idealizations because the idealizations let them \emph{think}.

Consider the path to general relativity.
Einstein's 1915 field equations $G_{\mu\nu} = 8\pi T_{\mu\nu}$ are a finite system of PDEs relating finite objects---metric components, their derivatives, stress-energy.
Writing them down requires no idealization; the route to them through differential geometry and tensor calculus is algebraic and BISH\@.
But Einstein arrived at these equations by thinking of spacetime as a smooth manifold, gravity as curvature, geodesics as paths of free particles.
That geometric picture, while not formally requiring non-constructive logic, is deeply entangled with the idea of a completed continuum---a smooth, infinite, everywhere-defined mathematical object.
The picture guided ten years of creative struggle (1905--1915).

Once the equations were written, every empirical prediction Einstein extracted was BISH\@.
The perihelion precession of Mercury: a perturbative solution of the geodesic equation in the Schwarzschild metric, yielding $\delta\varphi = 6\pi GM/(c^2 a(1-e^2))$.
Finite computation, algebraic result.
Gravitational redshift: $\nu_2/\nu_1 = \sqrt{g_{00}(r_1)/g_{00}(r_2)}$.
One formula, one substitution.
Gravitational lensing: $\delta = 4GM/(c^2 b)$.
A definite integral with an explicit integrand.
Every number Einstein compared with observation was a BISH computation from specific equations evaluated at specific parameters.

The same pattern holds for quantum mechanics.
Heisenberg's 1925 matrix mechanics was explicitly finite and algebraic---transition amplitudes as finite matrix elements, the hydrogen spectrum by finite matrix truncation.
This is BISH\@.
Schr\"odinger's 1926 wave mechanics introduced the wave function $\psi(x) \in L^2(\mathbb{R}^3)$---an infinite-dimensional Hilbert space---but every calculation Schr\"odinger actually performed reduced to solving a specific differential equation with specific boundary conditions.
The hydrogen eigenvalue $E_n = -13.6/n^2$~eV comes from a boundary-value problem for a second-order ODE; each specific eigenvalue is computable by algebraic manipulation.
No spectral theorem is invoked.
The spectral theorem enters when you assert that these are \emph{all} the eigenvalues and that the eigenfunctions form a \emph{complete} basis---an assertion about a completed infinite object that organizes the physics but generates no additional predictions.

The idealizations serve as \emph{cognitive infrastructure}: they convert processes into objects.
The thermodynamic limit converts an open-ended approximation (``the free energy per site is within~$\varepsilon$ of $f(\beta)$ for lattice size $N(\varepsilon)$'') into a definite fact (``the free energy is $f(\beta)$'').
The first is a bound you can compute with.
The second is a thought you can compose with other thoughts---you can differentiate it, take its Legendre transform, study its singularities.
The spectral theorem converts an open-ended list (``these specific eigenvalues satisfy these specific equations'') into a completed structure (``every self-adjoint operator has a spectral decomposition'').
The first handles specific systems.
The second enables general theory---perturbation theory, scattering theory, the classification of quantum symmetries.
Each idealization converts a BISH computation into a mathematical object that can be manipulated, composed, and reasoned about at a higher level of abstraction.
The logical cost, measured by the calibration table, is the price of that conversion.

This reinterpretation answers the essential-idealizations objection directly.
Batterman~\cite{Batterman2005} argues that infinite idealizations are ``explanatorily essential''---that the thermodynamic limit genuinely explains universality in a way finite-system descriptions do not.
We can now agree partially: the idealization is \emph{cognitively} essential, in the sense that it enables reasoning, explanation, and theory-building that the finite descriptions cannot support at comparable cognitive cost.
But it is not \emph{computationally} essential: every number the explanation predicts is extractable from the BISH cellar.
The cathedral is not a computing device.
It is a thinking device.
Its value is real.
Its logical cost is measurable.
Its computational content is zero.

The calibration table, read through this lens, becomes a cost-benefit analysis of idealization.
Not all idealizations are equal.
The thermodynamic limit (LPO) converts approximation processes into definite thermodynamic potentials, enabling all of equilibrium statistical mechanics---phase transitions, critical exponents, universality.
High cognitive return on the logical investment.
The Penrose singularity (LPO) converts finite-time geodesic focusing into a definite incompleteness theorem, enabling the entire programme of black hole physics.
High cognitive return.
The singular states of the bidual (WLPO) produce a mathematical object---a functional that vanishes on all compact operators---that no experiment can prepare and no physical reasoning builds upon.
Low cognitive return.
The calibration table provides the cost side of this ledger; the history of physics provides the benefit side.
Together, they distinguish productive idealizations from pathological ones---not by taste, but by measurement.

The engineering confirms this assessment.
Every technology based on twentieth-century physics---GPS, semiconductors, lasers, MRI, nuclear energy---uses specific finite computations at BISH\@.
The relativistic corrections in GPS (${\sim}38$~microseconds per day, compensating the net effect of special-relativistic time dilation and general-relativistic gravitational blueshift) are arithmetic: one algebraic formula from the Schwarzschild metric evaluated at the satellite's orbital parameters.
The atomic clock frequency (cesium-133 hyperfine transition at 9,192,631,770~Hz) is computed from specific quantum-mechanical matrix elements.
No spectral theorem, no completed Hilbert space, no thermodynamic limit appears in any engineering specification.
The cathedral guides the theorist's thinking.
The cellar runs the devices.
```


## EDIT 7: Revise the Batterman objection response
## Location: The paragraph starting with "\emph{``What about essential idealizations?''}"
## at approximately line 1212-1217.
## Anchor string (unique): "What about essential idealizations?"
## Action: REPLACE the existing response (lines 1212-1217) with a shorter
## version that cross-references the new subsection instead of punting.

REPLACE the block:
```
\emph{``What about essential idealizations?''}
Batterman \cite{Batterman2005} has argued that infinite idealizations are ``explanatorily essential''---that the thermodynamic limit, for instance, is not merely a convenience but genuinely explains universality and critical phenomena in a way that finite-system descriptions do not.
Our results address \emph{predictive} content, not \emph{explanatory} content.
The finite-size error bounds reproduce every number a laboratory can measure.
Whether the \emph{explanatory power} of universality classes and critical exponents can be captured without the completed limit is an open question---one of the most important in the philosophy of physics \cite{vanWierst2019}.
We take no position on it here.
```

WITH:
```latex
\emph{``What about essential idealizations?''}
Batterman \cite{Batterman2005} has argued that infinite idealizations are ``explanatorily essential''---that the thermodynamic limit, for instance, is not merely a convenience but genuinely explains universality and critical phenomena in a way that finite-system descriptions do not.
We now take a position.
The idealizations are \emph{cognitively} essential: they convert BISH processes into mathematical objects that can be composed, differentiated, and reasoned about at a level of abstraction that finite descriptions cannot match at comparable cognitive cost (Section~7).
But they are not \emph{computationally} essential: every number the explanation generates is extractable at BISH\@.
The calibration table measures the logical cost of this cognitive infrastructure.
The cost is real; the benefit is real; the computational content is zero.
```


## EDIT 8: Soften the "mathematical imperialism" line
## Location: Line 511
## Anchor string (unique): "a finite, operational physical theory was recast in the language of infinite-dimensional functional analysis, and the physics community gradually lost the ability to distinguish the physics from the formalism"
## Action: REPLACE this sentence with a more balanced version that
## acknowledges the cognitive value while noting the cost.

REPLACE:
```
This was a masterwork of mathematical architecture.
It was also an act of mathematical imperialism: a finite, operational physical theory was recast in the language of infinite-dimensional functional analysis, and the physics community gradually lost the ability to distinguish the physics from the formalism.
```

WITH:
```latex
This was a masterwork of mathematical architecture---and a consequential trade.
A finite, operational physical theory was recast in the language of infinite-dimensional functional analysis, gaining enormous conceptual power (general spectral theory, representation theory, the classification of quantum symmetries) at a logical cost that would remain invisible for ninety years.
The physics community gained a thinking tool of extraordinary scope and gradually lost the ability to distinguish the physics from the tool.
```


# ================================================================
# SUMMARY OF PART 2 CHANGES
# ================================================================
#
# Edit 6: ~55 lines inserted after the keymessage in Section 7
#          (new subsection "The cognitive value of idealization")
# Edit 7: 6 lines replaced with 6 lines (Batterman objection,
#          now cross-references Section 7 instead of punting)
# Edit 8: 2 lines replaced with 3 lines (line 510-511, softened
#          "mathematical imperialism" to "consequential trade")
#
# Total new content: ~58 lines of LaTeX
#
# STRUCTURAL NOTE: Edit 6 adds a subsection* (unnumbered) within
# Section 7. This does not change the section numbering. The
# cross-reference in Edit 7 to "Section 7" should work since the
# new subsection is inside Section 7.
#
# VERIFICATION: After edits, search for these strings to confirm:
# - "The cognitive value of idealization" (Edit 6 heading present)
# - "the idealizations let them \\emph{think}" (Edit 6 present)
# - "The cathedral is not a computing device" (Edit 6 present)
# - "We now take a position" (Edit 7 present)
# - "consequential trade" (Edit 8 present)
# - "gradually lost the ability to distinguish" still present (Edit 8 preserves core idea)
#
# IMPORTANT: These edits should be applied AFTER Edits 1-5 from
# the previous instruction file (essay_edit_instructions.md).
# Edits 1-5 handle: Born rule paragraph, spectrum paragraph,
# unifying observation, Cubitt/MIP* expansion, Ji et al. bibentry.
# ================================================================
