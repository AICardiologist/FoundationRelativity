# Senior Consultant's Strategy for Smooth Case (Future Reference)

## Executive Summary
The senior math AI consultant strongly endorses our "discrete first" strategy and provides a concrete roadmap for the eventual smooth case implementation using the Implicit Function Theorem (IFT) approach.

## Key Insights

### 1. 2D Conformal Advantage
Since our bump perturbations are isotropic in 2D, they are conformal. This gives us:
- Simplified Laplacian transformation: $\Delta_{\tilde{g}} = e^{-2\phi} \Delta_g$
- Cleaner variation formula: $\dot{\lambda}_1(0) = -\lambda_1(0) \int_M u_1^2 \dot{\phi}(0) \, d\text{vol}_{g_0}$
- No need for $|\nabla u|^2$ bounds to determine sign of shift

### 2. IFT Approach (Avoiding Kato-Rellich)
Instead of formalizing abstract perturbation theory:
1. Define map $F(\varepsilon, \lambda, u) = 0$ encoding eigenvalue problem
2. Use Implicit Function Theorem (already in mathlib)
3. Prove Fréchet derivative invertibility
4. Get smooth dependence $\lambda_1(\varepsilon)$

### 3. Recommended Axiomatizations
- **Lemma 3.8** (Thin-Neck Harnack) - bulk constancy of eigenfunction
- **Eigenvalue simplicity** - first non-zero eigenvalue is simple
- **Elliptic regularity** estimates

## Implementation Phases (When Ready)

### Phase 1: Geometric Setup
- Formalize Sobolev spaces $(L^2(M), H^1(M), H^2(M))$
- 2D conformal Laplacian transformation law

### Phase 2: Differentiability via IFT
- Setup functional analytic framework
- Prove eigenvalue simplicity
- Apply IFT for smooth dependence

### Phase 3: Variation Formula
- Derive simplified conformal variation
- Axiomatize bulk constancy (Lemma 3.8)

### Phase 4: Quantitative Bounds
- Combine variation + axioms
- Prove bump_shift theorem

## Collaboration Recommendations

### Lean Zulip Engagement
- Post in #maths stream
- Highlight "shape-derivative toolbox" need
- Appeal to SpectralThm project team

### Key Expertise Needed
- **Functional Analysis**: SpectralThm project members
- **Differential Geometry**: Sébastien Gouëzel, Heather Macbeth
- **Elliptic PDE**: For regularity estimates

## Current Priority
Per consultant: **"Implement 1A → 2 → 3 → 6 first"**
- Complete discrete CPW model
- Secure main undecidability result
- Pursue smooth case as long-term, high-value effort

This aligns perfectly with our current Phase 1B work on the discrete model.