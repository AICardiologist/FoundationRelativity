# Fermion Mass Hierarchy: Phase 2 Investigation

## Beyond One-Loop, Small-Step-Size, Individual-Coupling Scans

**Author:** Paul Chun-Kit Lee  
**Date:** February 2026  
**Status:** Exploratory computation — Phase 2 (follows Phase 1 results)  
**Prerequisite:** Phase 1 script `paper18/rg_mass_hierarchy.py` should be available for reference. Reuse its infrastructure (gauge coupling beta functions, physical constants, RK4 integrator) where possible.

---

## 0. Context: What Phase 1 Found and What It Didn't Test

Phase 1 tested whether the **one-loop** SM Yukawa beta functions, treated as a discrete RK4 map at **small step size**, have attractor structure in **individual coupling** space that produces the mass hierarchy from generic initial conditions.

Results: The top quasi-fixed-point (QFP) was confirmed and is visible at N=10 steps (BISH). The full mass hierarchy is not an attractor. The Koide ratio doesn't emerge generically.

**Phase 1 tested a narrow special case of a broad hypothesis.** Five substantive alternatives were not tested. This document specifies all five. Each investigation is self-contained with its own success criteria.

**Output:** A single Python script `paper18/rg_phase2.py` that runs all five investigations sequentially, producing diagnostic plots in `paper18/plots_phase2/`. Target runtime: under 30 minutes total.

---

## Investigation 1: Two-Loop Beta Functions — New QFPs at Higher Loop Order?

### 1.1 Motivation

The original CRM-motivated hypothesis was that the mass hierarchy is a **perturbative** phenomenon — visible at the right loop order. If the one-loop QFP determines the top, perhaps two-loop corrections create additional fixed-point structure for the bottom and tau. Each generation at a successively higher loop order, with hierarchy from loop suppression α/(4π) ≈ 10⁻³.

Phase 1 only ran one-loop. This is the most important gap to fill.

### 1.2 Two-Loop Beta Functions

The full two-loop Yukawa beta functions are given in:

> M.-x. Luo, H.-w. Wang, Y. Xiao, "Two-loop renormalization group equations in the Standard Model," Phys. Rev. D 67, 065019 (2003). arXiv:hep-ph/0211440.

The two-loop correction to the top Yukawa beta function has the schematic form:

```
(16π²)² β_yt^(2) = y_t [ 
    -12 y_t⁴ + ... (Yukawa⁴ terms)
    + y_t² (Ag₃² + Bg₂² + Cg₁²) + ... (Yukawa²×gauge² terms)  
    + (Dg₃⁴ + Eg₂⁴ + Fg₁⁴ + cross terms) + ... (gauge⁴ terms)
]
```

The exact coefficients are lengthy. **Approach:** Use the coefficients from Luo-Wang-Xiao Table I. If manual transcription is impractical, use the well-known approximate forms.

**Simplified two-loop implementation (acceptable for this investigation):**

For the third-generation Yukawa couplings, the dominant two-loop corrections come from:
- QCD: -108 g₃⁴ y_t (large, drives y_t further toward QFP)
- Top self-coupling: -12 y_t⁵ (slows growth of y_t)
- Mixed terms: various y_t³ g² terms

At minimum, implement the **two-loop gauge coupling** beta functions (well-known, compact) combined with **one-loop Yukawa** beta functions. This captures the leading two-loop effect (gauge running feeds into Yukawa evolution at next order).

Two-loop gauge coupling beta functions:

```
(16π²)² dg₁/dt = g₁³ [199/18 g₁² + 9/2 g₂² + 44/3 g₃² - 17/6 y_t² - 5/6 y_b² - 5/2 y_τ²]
(16π²)² dg₂/dt = g₂³ [3/2 g₁² + 35/6 g₂² + 12 g₃² - 3/2 y_t² - 3/2 y_b² - 1/2 y_τ²]  
(16π²)² dg₃/dt = g₃³ [11/6 g₁² + 9/2 g₂² - 26 g₃² - 2 y_t² - 2 y_b²]
```

The total beta function at two-loop is:
```
β(g) = β^(1)(g)/(16π²) + β^(2)(g)/(16π²)²
```

### 1.3 What to Compute

1. Implement the system with two-loop gauge + one-loop Yukawa beta functions.
2. Repeat the Phase 1 scan: 1000 random initial conditions at Planck scale, run to EW scale.
3. Compare the QFP structure:
   - Does y_t still have a QFP? (Expected: yes, slightly shifted.)
   - Does y_b/y_t have a QFP that was absent at one loop?
   - Does y_τ/y_t have a QFP that was absent at one loop?
4. Plot: y_b(EW)/y_t(EW) distribution at one-loop vs two-loop. Are the distributions different? Is the two-loop distribution *narrower* (stronger attractor)?

### 1.4 Success Criterion

If the two-loop distribution of y_b/y_t is significantly narrower than the one-loop distribution (e.g., std reduced by >50%), or if a new fixed-point value appears, that's evidence for loop-order-dependent QFP structure.

### 1.5 Plot

`inv1_two_loop_comparison.png`: Side-by-side histograms of y_b/y_t at EW scale, one-loop vs two-loop, with observed value marked.

---

## Investigation 2: Large Step-Size Discrete Dynamics

### 2.1 Motivation

Phase 1 used small step sizes (dt ≈ 0.04) where the discrete RK4 map faithfully approximates the continuous ODE. But the CRM hypothesis is that the discrete map, **as a dynamical system in its own right**, might have different structure than the continuous flow.

Discrete maps can exhibit phenomena absent in continuous flows: period-2 orbits, bifurcations, chaos. These emerge at **large step sizes** where the map diverges from the ODE. The logistic map x → rx(1-x) is the canonical example: trivial as a continuous flow, rich as a discrete map.

If the Yukawa RG map at large step size exhibits bifurcation structure that organizes the couplings into a hierarchy, that would be genuinely new — a BISH phenomenon with no LPO analogue.

### 2.2 What to Compute

Use the **one-loop Euler map** (not RK4 — Euler is the "purest" discrete map):

```python
y_new = y + dt * beta(y, g)
g_new = g + dt * beta_g(g)
```

The full t-range is ln(M_Planck/M_Z) ≈ 39.4.

1. Fix initial conditions at observed Planck-scale values (run the known EW values backward to Planck scale using Phase 1's infrastructure).
2. Run the Euler map forward from Planck to EW using N steps, for N = 3, 5, 7, 10, 15, 20, 30, 50, 100, 500.
3. For each N, record all 9 Yukawa couplings at the EW scale.
4. Plot y_t(EW) vs N. The curve should converge to the ODE value as N → ∞. But does it exhibit non-monotone behavior at small N?
5. More interestingly: plot the **mass ratios** y_t/y_b, y_t/y_τ, y_b/y_τ as functions of N. Do the ratios stabilize at a different value for small N than for large N?
6. **Bifurcation diagram:** For fixed initial y_t = 3.0, vary the "effective coupling" by scanning N from 2 to 100. For each N, record y_t after the N steps. Plot y_t(final) vs N. Look for period-doubling or bifurcation structure.

### 2.3 What Would Be Interesting

- If mass ratios at small N (say N=5) are **closer** to observed values than at large N, the discrete structure is doing something the continuous limit destroys.
- If the bifurcation diagram shows non-trivial structure (period-2 orbits, windows of stability), the Yukawa RG has discrete dynamics worth studying.
- If everything is monotone convergence to the ODE value, the discrete map adds nothing. (This is the expected outcome for well-behaved ODEs, but Yukawa beta functions are nonlinear — worth checking.)

### 2.4 Success Criterion

Any non-monotone structure in mass ratios vs N, or any bifurcation in the Euler map at small N.

### 2.5 Plots

`inv2_coupling_vs_N.png`: y_t(EW) and y_b(EW) vs N (step count), with ODE limit marked.  
`inv2_ratios_vs_N.png`: Mass ratios y_t/y_b, y_b/y_τ vs N, with observed values marked.  
`inv2_bifurcation.png`: y_t(final) vs N for fixed initial y_t = 3.0.

---

## Investigation 3: Ratio-Space Fixed Points

### 3.1 Motivation

Phase 1 scanned individual Yukawa couplings and looked for fixed points in coupling *values*. But the mass hierarchy is about *ratios*. The RG equations for ratios can have different fixed-point structure.

Define:
```
r_b = y_b / y_t
r_τ = y_τ / y_t  
r_c = y_c / y_t
r_s = y_s / y_t
...etc
```

The beta function for r_b = y_b/y_t is:
```
dr_b/dt = r_b × [β_yb/y_b - β_yt/y_t]
```

Fixed points of this equation satisfy β_yb/y_b = β_yt/y_t. These are **not** the same as fixed points of the individual couplings. In particular, r_b = 0 is always a fixed point (stable: if bottom starts infinitely lighter than top, it stays that way). But there might be nontrivial fixed points at r_b* ≈ 0.024 (the observed ratio at EW scale).

### 3.2 What to Compute

1. Derive the one-loop beta functions for the ratios r_b = y_b/y_t, r_τ = y_τ/y_t analytically:

```python
def beta_rb(r_b, r_tau, y_t, g1, g2, g3):
    """Beta function for r_b = y_b / y_t."""
    # beta_yb / y_b - beta_yt / y_t
    # = [9/2 y_b² + 3/2 y_t² + y_τ² - 8g₃² - 9/4 g₂² - 5/12 g₁²]
    #   - [9/2 y_t² + 3/2 y_b² + y_τ² - 8g₃² - 9/4 g₂² - 17/12 g₁²]
    # = (9/2 - 3/2)(y_b² - y_t²) + (-5/12 + 17/12) g₁²
    # = 3(y_b² - y_t²) + g₁²
    # = 3 y_t² (r_b² - 1) + g₁²
    return r_b * (3 * y_t**2 * (r_b**2 - 1) + g1**2) / (16 * np.pi**2)
```

Note the dramatic simplification: many terms cancel in the ratio. The beta function for r_b depends on y_t² (r_b² - 1) + g₁². For r_b << 1 (which is the physical regime), this is approximately:

```
dr_b/dt ≈ r_b × (-3 y_t² + g₁²) / (16π²)
```

If 3 y_t² > g₁², then dr_b/dt < 0 (r_b flows to zero — the bottom decouples further from the top). If 3 y_t² < g₁², then dr_b/dt > 0 (r_b grows). The crossover at y_t² = g₁²/3 might create a fixed point in the coupled system.

**Important: verify this derivation.** I may have the one-loop coefficients slightly wrong. Rederive from the full beta functions in Phase 1's code.

2. Scan initial conditions in ratio space: r_b(Planck) ∈ [10⁻⁴, 1], r_τ(Planck) ∈ [10⁻⁴, 1], with y_t(Planck) ∈ [0.5, 5]. Run to EW scale.

3. Plot r_b(EW) vs r_b(Planck) for fixed y_t(Planck) = 2.0. Look for flattening (indicating a QFP in ratio space).

4. Repeat for r_τ.

5. **2D ratio-space portrait:** For fixed y_t at QFP value, plot (r_b(EW), r_τ(EW)) for a grid of initial (r_b, r_τ). Does the flow converge to a point, a line, or scatter?

### 3.3 Success Criterion

If r_b(EW) converges to ≈ 0.024 (observed) for a significant fraction of initial r_b values, that's a ratio-space QFP for the b/t mass ratio. Similarly for r_τ → 0.010 (observed).

### 3.4 Plots

`inv3_rb_convergence.png`: r_b(EW) vs r_b(Planck) for various y_t(Planck).  
`inv3_rtau_convergence.png`: r_τ(EW) vs r_τ(Planck) for various y_t(Planck).  
`inv3_ratio_plane.png`: 2D scatter of (r_b(EW), r_τ(EW)) from grid of initial conditions, with observed point marked.

---

## Investigation 4: Threshold-Corrected Piecewise RG

### 4.1 Motivation

This is the most CRM-native investigation. In the real Standard Model, the RG does not run smoothly from Planck to EW. Particles decouple at their mass thresholds. Below each threshold, the beta function changes because the decoupled particle no longer contributes to loops.

The thresholds (in GeV, approximate):
```
m_t ≈ 173    (top decouples)
m_H ≈ 125    (Higgs decouples)  
m_Z ≈ 91.2   (Z decouples)
m_W ≈ 80.4   (W decouples)
m_b ≈ 4.18   (bottom decouples)
m_τ ≈ 1.78   (tau decouples)
m_c ≈ 1.27   (charm decouples)
```

This is **inherently discrete**: a finite sequence of beta function changes at specific scales. The continuous RG flow is an idealization; the physical RG is a piecewise computation with finitely many pieces. This is naturally BISH.

The critical observation: **the mass hierarchy determines the thresholds, which determine the piecewise RG, which feeds back on the mass predictions.** This self-consistency condition (masses → thresholds → running → masses) is a finite algebraic system.

### 4.2 What to Compute

**Step 1: Implement piecewise one-loop RG.**

Define the effective number of active flavors at each scale. Below each fermion threshold, remove that fermion's contribution from the beta functions.

```python
def n_active_fermions(mu, masses):
    """Return which fermions are active at scale mu."""
    active = {}
    for name, mass in masses.items():
        active[name] = (mu > mass)
    return active

def beta_yukawa_piecewise(y, g, mu, masses):
    """One-loop beta functions with threshold corrections."""
    active = n_active_fermions(mu, masses)
    # Only include contributions from active fermions in loops
    # Modify gauge beta function coefficients based on active fermions
    ...
```

The gauge coupling beta function coefficients change with the number of active fermions:
- b₃ = -11 + 2/3 n_f (where n_f = number of active quark flavors)
- b₂ = -22/3 + 2/3 n_f + 1/6 n_H (n_H = number of active Higgs doublets)
- b₁ depends on hypercharges of active fermions

**Step 2: Self-consistency iteration.**

1. Start with a guess for the fermion masses (e.g., observed values).
2. Compute thresholds from the guessed masses.
3. Run the piecewise RG from Planck to each threshold scale.
4. Read off the Yukawa couplings at each threshold. Compute predicted masses: m_f = y_f × v/√2.
5. Compare predicted masses with the guessed masses.
6. Iterate until convergence (fixed-point iteration).

**Step 3: Sensitivity analysis.**

Start with a *uniform* guess (all fermion masses equal, say 10 GeV). Iterate the self-consistency condition. Does it converge to the observed hierarchy, or to something else?

Try several initial guesses:
- All masses = 1 GeV
- All masses = 10 GeV
- All masses = 100 GeV
- Random masses from [0.1, 100] GeV

### 4.3 What Would Be Interesting

If the self-consistency iteration has a unique fixed point (or a small discrete set of fixed points), and one of them matches the observed hierarchy, then the mass hierarchy is **determined** by the piecewise BISH structure of the SM. The continuous-flow approximation misses this because it doesn't resolve the thresholds.

If the iteration doesn't converge, or converges to something far from observed, the self-consistency condition has a solution space that includes the observed hierarchy as one point among many — the hierarchy requires additional UV input.

### 4.4 Success Criterion

If the self-consistency iteration converges to approximately correct mass ratios from more than one initial guess, that's evidence for threshold-corrected BISH structure determining the hierarchy.

### 4.5 Plots

`inv4_self_consistency.png`: Mass ratios (m_t/m_b, m_b/m_τ, m_c/m_s) vs iteration number for various initial guesses.  
`inv4_convergence_basin.png`: For a 2D slice of initial conditions (e.g., initial m_t and m_b with others fixed), color-code by which fixed point the iteration converges to.

---

## Investigation 5: Koide Phase Dynamics in Circulant Parameterization

### 5.1 Motivation

The Koide formula for charged leptons can be parameterized as:

```
√m_n = μ (1 + √2 cos(δ + 2πn/3)),  n = 0, 1, 2
```

where μ sets the overall scale and δ ≈ 0.2222 ≈ 2/9 sets the mass ratios. The entire charged lepton mass spectrum is determined by two parameters. The Koide ratio Q = 2/3 holds identically for any δ in this parameterization — it's a consequence of the circulant structure, not a coincidence.

Phase 1 checked whether Q ≈ 2/3 emerges from RG evolution (it doesn't). But we didn't check whether **the phase δ** has a dynamical origin.

### 5.2 What to Compute

**Step 1: Implement the circulant parameterization.**

Given Yukawa couplings (y_e, y_μ, y_τ), extract (μ, δ):

```python
import numpy as np

def yukawas_to_circulant(y_e, y_mu, y_tau):
    """Extract (mu, delta) from Yukawa couplings via Koide parameterization."""
    # sqrt(m) = sqrt(y * v / sqrt(2)) up to a constant
    # Work with sqrt(y) instead
    s = np.array([np.sqrt(y_e), np.sqrt(y_mu), np.sqrt(y_tau)])
    
    # mu = (s[0] + s[1] + s[2]) / 3  (the DC component)
    # The circulant decomposition: s_n = mu * (1 + sqrt(2) * cos(delta + 2*pi*n/3))
    # Solve for mu and delta from the three values
    
    mu = np.sum(s) / 3.0
    
    # From the parameterization:
    # s_n / mu - 1 = sqrt(2) * cos(delta + 2*pi*n/3)
    # Use n=0 and n=1 to solve for delta
    
    if mu <= 0:
        return None, None
    
    c0 = (s[0] / mu - 1) / np.sqrt(2)
    c1 = (s[1] / mu - 1) / np.sqrt(2)
    
    # c0 = cos(delta), c1 = cos(delta + 2*pi/3)
    # Solve for delta using atan2
    # c1 = cos(delta)cos(2pi/3) - sin(delta)sin(2pi/3)
    #    = -0.5 cos(delta) - (sqrt(3)/2) sin(delta)
    # So: c1 = -0.5 c0*sqrt(2)*mu/mu... 
    # Better: use discrete Fourier transform
    
    # DFT approach: Z = sum_n s_n * exp(-2*pi*i*n/3)
    omega = np.exp(-2j * np.pi / 3)
    Z = s[0] + s[1] * omega + s[2] * omega**2
    
    delta = -np.angle(Z)  # phase of the first Fourier mode
    amp = np.abs(Z) / (mu * 3)  # should be ≈ sqrt(2) if parameterization is exact
    
    return mu, delta

def circulant_to_yukawas(mu, delta):
    """Reconstruct sqrt(Yukawa) from (mu, delta)."""
    s = np.array([
        mu * (1 + np.sqrt(2) * np.cos(delta + 2*np.pi*n/3))
        for n in range(3)
    ])
    return s**2  # return y, not sqrt(y)
```

**Step 2: Run RG in circulant coordinates.**

1. Start with various initial (μ, δ) at the Planck scale.
2. At each RG step, convert (μ, δ) → (y_e, y_μ, y_τ), compute the beta functions in Yukawa space, step forward, then convert back to (μ, δ).
3. Track (μ(t), δ(t)) as functions of scale.

**Step 3: Look for fixed points in δ.**

- Plot δ(EW) vs δ(Planck) for fixed μ. Does δ converge to a preferred value?
- Specifically: does δ converge to ≈ 2/9 ≈ 0.2222?
- Also check: is the amplitude (should be √2 for exact Koide) preserved, enhanced, or destroyed by RG evolution?

**Step 4: Flow portrait in (μ, δ) space.**

For a grid of initial (μ, δ) at Planck scale (μ ∈ [10⁻⁴, 10⁻¹], δ ∈ [0, 2π/3]), plot the flow arrows and endpoints at EW scale. Look for fixed points, limit cycles, or attracting regions.

### 5.3 Success Criterion

If δ(EW) converges to ≈ 2/9 from a range of initial δ values, the Koide phase has a dynamical (RG) origin. This would be a genuine discovery — explaining the Koide formula as an infrared fixed point in circulant parameterization space.

If δ(EW) is sensitive to δ(Planck) (no convergence), the Koide formula's phase is UV-sensitive and requires explanation from high-energy physics.

### 5.4 Plots

`inv5_delta_convergence.png`: δ(EW) vs δ(Planck) for various μ(Planck).  
`inv5_flow_portrait.png`: (μ, δ) flow portrait from Planck to EW, with observed point marked.  
`inv5_amplitude_evolution.png`: Koide amplitude (should be √2) vs scale, for initial conditions near the observed values.

---

## Implementation Notes

### General Structure

```python
"""
paper18/rg_phase2.py — Phase 2 investigations for the fermion mass hierarchy.

Reuses infrastructure from rg_mass_hierarchy.py (Phase 1):
- Physical constants (gauge couplings, masses, v)
- One-loop beta functions
- RK4 integrator
- Plotting utilities

New in Phase 2:
- Two-loop gauge beta functions (Investigation 1)
- Euler map at variable step size (Investigation 2)
- Ratio-space beta functions (Investigation 3)
- Piecewise RG with thresholds (Investigation 4)
- Circulant parameterization (Investigation 5)
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.integrate import solve_ivp
import os

OUTPUT_DIR = "paper18/plots_phase2"
os.makedirs(OUTPUT_DIR, exist_ok=True)
```

### Physical Constants

Reuse from Phase 1. Key values:

```python
v = 246.22  # Higgs VEV (GeV)
MZ = 91.1876  # Z mass (GeV)
M_PLANCK = 1.22e19  # Planck mass (GeV)
t_range = np.log(M_PLANCK / MZ)  # ≈ 39.4

# Gauge couplings at M_Z (MSbar, GUT normalized for g1)
g1_MZ = 0.3574
g2_MZ = 0.6518
g3_MZ = 1.221

# Fermion masses (GeV, PDG 2024)
masses = {
    't': 172.57, 'b': 4.18, 'tau': 1.777,
    'c': 1.27, 's': 0.0934, 'mu': 0.10566,
    'u': 0.00216, 'd': 0.00467, 'e': 0.000511
}

# Tree-level Yukawas: y_f = sqrt(2) * m_f / v
yukawas_EW = {f: np.sqrt(2) * m / v for f, m in masses.items()}
```

### Runtime Budget

- Investigation 1 (two-loop scan): ~5 min (1000 samples, same as Phase 1 with modified betas)
- Investigation 2 (large step-size): ~2 min (one set of initial conditions, 10 values of N)
- Investigation 3 (ratio-space): ~5 min (grid scan in 2D ratio space)
- Investigation 4 (threshold self-consistency): ~5 min (iteration with piecewise RG)
- Investigation 5 (Koide phase): ~5 min (grid scan in (μ, δ) space)
- Total: ~22 min

### Output Summary

Each investigation should print a summary of its findings to stdout, in this format:

```
=== Investigation N: [Title] ===
Key finding: [one sentence]
Observed vs expected: [numbers]
Success criterion met: YES / NO / PARTIAL
Plot saved: [filename]
```

At the end, print an overall summary:

```
=== PHASE 2 OVERALL ===
Investigation 1 (two-loop QFPs): [result]
Investigation 2 (large step-size): [result]
Investigation 3 (ratio-space): [result]
Investigation 4 (thresholds): [result]
Investigation 5 (Koide phase): [result]
New findings beyond Phase 1: [count]/5
```

---

## Success Criteria Summary

| # | Investigation | What would be new | Success criterion |
|---|---|---|---|
| 1 | Two-loop beta functions | New QFP for y_b/y_t at two-loop | Distribution of y_b/y_t narrows by >50% vs one-loop |
| 2 | Large step-size dynamics | Bifurcation or non-monotone structure in discrete map | Any non-monotone mass ratio vs N |
| 3 | Ratio-space fixed points | QFP for r_b = y_b/y_t ≈ 0.024 | r_b(EW) converges for >20% of initial conditions |
| 4 | Threshold self-consistency | Hierarchy from piecewise BISH structure | Convergence to observed ratios from >1 initial guess |
| 5 | Koide phase dynamics | δ → 2/9 as infrared attractor | δ(EW) converges for >20% of initial δ values |

Any single success would justify further investigation. If all five are negative, we can confidently conclude that the SM's infrared dynamics do not determine the mass hierarchy in any parameterization or at any loop order, and the hierarchy requires genuine UV input.
